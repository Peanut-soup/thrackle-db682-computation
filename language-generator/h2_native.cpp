// Exhaustive H2 extension generator. No frozen H2 data or DB search is used.
// Compile: g++ -O3 -std=c++17 -pthread h2_native.cpp -o h2_native
// Windows: cl /O2 /EHsc /std:c++17 /I PATH_TO_BOOST h2_native.cpp /Fe:h2_native.exe
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/boyer_myrvold_planar_test.hpp>
#include <boost/version.hpp>
#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <mutex>
#include <set>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

using Rows = std::array<std::vector<int>,9>;
using Record = std::array<unsigned char,12>;
using Graph = boost::adjacency_list<boost::vecS,boost::vecS,boost::undirectedS>;
constexpr int DB[9] = {0,1,11,10,9,8,7,6,2};
// Cycle vertices: A,s1,B,q5,q4,q3,q2,q1; private H2 vertex: p1=8.
// The tail is enumerated A->p1, opposite to its stored v0.15.0 direction.
constexpr int START[9] = {0,1,3,4,5,6,7,0,0};
constexpr int END[9]   = {1,2,2,3,4,5,6,7,8};
constexpr std::uint64_t FACT[7] = {1,1,2,6,24,120,720};
constexpr std::uint64_t POW6[7] = {1,6,36,216,1296,7776,46656};

struct Built {int vertices; std::vector<std::pair<int,int>> edges;};

void validate_rows(const Rows& rows, bool complete) {
    if (rows[8].size()>6 || (complete && rows[8].size()!=6))
        throw std::runtime_error("Invalid tail length");
    for(int e=0;e<9;++e) {
        std::set<int> unique;
        for(int f:rows[e]) {
            if(f<0||f>=9||f==e||!unique.insert(f).second)
                throw std::runtime_error("Malformed row");
            if(START[e]==START[f]||START[e]==END[f]||END[e]==START[f]||END[e]==END[f])
                throw std::runtime_error("Crossing of incident edges");
            if(std::count(rows[f].begin(),rows[f].end(),e)!=1)
                throw std::runtime_error("Asymmetric crossing pair");
        }
        if(e<8) {
            for(int f=0;f<8;++f) {
                bool independent = (e!=f && START[e]!=START[f] && START[e]!=END[f]
                                    && END[e]!=START[f] && END[e]!=END[f]);
                if((unique.count(f)!=0)!=independent)
                    throw std::runtime_error("Incomplete C8 row");
            }
        }
    }
}

Built build(const Rows& rows, bool complete) {
    int cross[9][9]; for(auto& row:cross) for(int& x:row) x=-1;
    int next=9;
    for(int e=0;e<9;++e) for(int f:rows[e]) if(e<f)
        cross[e][f]=cross[f][e]=next++;
    int arms[9][96][2]; for(auto& edge:arms) for(auto& arm:edge) arm[0]=arm[1]=-1;
    Built out; out.edges.reserve(220);
    for(int e=0;e<9;++e) {
        std::vector<int> route; route.reserve(15); route.push_back(START[e]);
        for(std::size_t i=0;i<rows[e].size();++i) {
            if(i) route.push_back(next++);
            route.push_back(cross[e][rows[e][i]]);
        }
        if(e!=8||complete) route.push_back(END[e]);
        for(std::size_t j=1;j<route.size();++j) out.edges.emplace_back(route[j-1],route[j]);
        for(std::size_t i=0;i<rows[e].size();++i) {
            int pos=1+2*int(i), x=route[pos];
            arms[e][x][0]=route[pos-1];
            if(pos+1<int(route.size())) arms[e][x][1]=route[pos+1];
        }
    }
    for(int e=0;e<9;++e) for(int f:rows[e]) if(e<f) {
        int x=cross[e][f];
        for(int a:arms[e][x]) for(int b:arms[f][x])
            if(a>=0&&b>=0) out.edges.emplace_back(a,b);
    }
    out.vertices=next;
    return out;
}

bool planar(const Built& built) {
    Graph graph(built.vertices);
    for(auto edge:built.edges) boost::add_edge(edge.first,edge.second,graph);
    return boost::boyer_myrvold_planarity_test(graph);
}

struct ParentResult {
    std::vector<Record> records;
    std::uint64_t nodes=0,tests=0,prunes=0,covered=0;
};

ParentResult generate(Rows rows) {
    validate_rows(rows,false);
    ParentResult result;
    auto visit = [&](auto&& self, unsigned mask)->void {
        ++result.nodes;
        if(!mask) {
            Record record{};
            for(int i=0;i<6;++i) record[i]=static_cast<unsigned char>(DB[rows[8][5-i]]);
            for(int i=0;i<6;++i) {
                auto at=std::find(rows[i+1].begin(),rows[i+1].end(),8);
                if(at==rows[i+1].end()) throw std::runtime_error("Missing tail crossing");
                record[i+6]=static_cast<unsigned char>(at-rows[i+1].begin());
            }
            result.records.push_back(record); ++result.covered;
            return;
        }
        for(int q=1;q<=6;++q) if(mask & (1u<<(q-1))) {
            unsigned rest=mask & ~(1u<<(q-1));
            int remaining=0; for(unsigned x=rest;x;x>>=1) remaining+=int(x&1);
            for(int gap=0;gap<6;++gap) {
                rows[q].insert(rows[q].begin()+gap,8); rows[8].push_back(q);
                ++result.tests;
                if(planar(build(rows,rest==0))) self(self,rest);
                else {++result.prunes; result.covered+=FACT[remaining]*POW6[remaining];}
                if(rows[8].back()!=q||rows[q][gap]!=8)
                    throw std::runtime_error("Restoration failure");
                rows[8].pop_back(); rows[q].erase(rows[q].begin()+gap);
            }
        }
    };
    visit(visit,63u);
    if(result.covered!=FACT[6]*POW6[6]) throw std::runtime_error("Parent coverage failure");
    std::sort(result.records.begin(),result.records.end());
    if(std::adjacent_find(result.records.begin(),result.records.end())!=result.records.end())
        throw std::runtime_error("Duplicate H2 record");
    return result;
}

std::vector<Rows> load(const std::string& filename) {
    std::ifstream file(filename,std::ios::binary);
    if(!file) throw std::runtime_error("Cannot read C8 input");
    std::vector<unsigned char> raw((std::istreambuf_iterator<char>(file)),{});
    if(raw.size()!=2544*40) throw std::runtime_error("Wrong C8 byte length");
    std::vector<Rows> parents(2544);
    for(int p=0;p<2544;++p) {
        for(int e=0;e<8;++e) for(int j=0;j<5;++j) {
            int label=raw[p*40+e*5+j], local=-1;
            for(int k=0;k<8;++k) if(DB[k]==label) local=k;
            if(local<0) throw std::runtime_error("Unknown C8 edge label");
            parents[p][e].push_back(local);
        }
        validate_rows(parents[p],false);
    }
    return parents;
}

// Probe mode exposes the exact native graph for independent differential tests.
void probe(const std::string& input,const std::string& output) {
    std::ifstream in(input); std::ofstream out(output);
    if(!in||!out) throw std::runtime_error("Cannot open probe file");
    int count; if(!(in>>count)||count<0) throw std::runtime_error("Bad probe count");
    for(int c=0;c<count;++c) {
        int complete; Rows rows;
        if(!(in>>complete)||(complete!=0&&complete!=1)) throw std::runtime_error("Bad completeness flag");
        for(auto& row:rows) {
            int length; if(!(in>>length)||length<0||length>6) throw std::runtime_error("Bad probe row length");
            for(int i=0;i<length;++i) {int value; if(!(in>>value)) throw std::runtime_error("Truncated row"); row.push_back(value);}
        }
        validate_rows(rows,complete!=0); auto b=build(rows,complete!=0);
        std::set<std::pair<int,int>> edges;
        for(auto e:b.edges) edges.insert(std::minmax(e.first,e.second));
        out<<int(planar(b))<<' '<<b.vertices<<' '<<edges.size();
        for(auto e:edges) out<<' '<<e.first<<' '<<e.second;
        out<<'\n';
    }
    if(!out) throw std::runtime_error("Probe write failed");
}

int main(int argc,char** argv) {
    try {
        if(argc==4&&std::string(argv[1])=="--probe") {probe(argv[2],argv[3]); return 0;}
        if(argc<4||argc>6) throw std::runtime_error("Usage: h2_native C8.raw H2.raw threads [start end]; or --probe input output");
        auto begin=std::chrono::steady_clock::now();
        auto parents=load(argv[1]); int threads=std::stoi(argv[3]);
        int start=argc==6?std::stoi(argv[4]):0, end=argc==6?std::stoi(argv[5]):2544;
        if(threads<1||threads>64||start<0||end>2544||end<=start||argc==5)
            throw std::runtime_error("Invalid range or thread count");
        std::vector<ParentResult> results(2544);
        std::atomic<int> next(start), completed(0); std::atomic<bool> failed(false);
        std::mutex mutex; std::string error;
        std::vector<std::thread> workers;
        for(int t=0;t<threads;++t) workers.emplace_back([&]{
            try {
                while(!failed) {
                    int p=next.fetch_add(1); if(p>=end) break;
                    results[p]=generate(parents[p]); int done=++completed;
                    if(done%64==0||done==end-start) {
                        std::lock_guard<std::mutex> guard(mutex);
                        std::cerr<<"H2 parents completed: "<<done<<'/'<<end-start<<std::endl;
                    }
                }
            } catch(const std::exception& e) {
                std::lock_guard<std::mutex> guard(mutex); failed=true; error=e.what();
            }
        });
        for(auto& worker:workers) worker.join();
        if(failed||completed!=end-start) throw std::runtime_error("Worker failed: "+error);
        std::ofstream out(argv[2],std::ios::binary);
        if(!out) throw std::runtime_error("Cannot create H2 output");
        std::uint64_t records=0,nodes=0,tests=0,prunes=0,covered=0;
        for(int p=start;p<end;++p) {
            const auto& r=results[p]; records+=r.records.size(); nodes+=r.nodes;
            tests+=r.tests; prunes+=r.prunes; covered+=r.covered;
            for(auto record:r.records) {
                out.put(static_cast<char>(p&255)); out.put(static_cast<char>((p>>8)&255));
                out.write(reinterpret_cast<const char*>(record.data()),12);
            }
        }
        out.close(); if(!out) throw std::runtime_error("H2 output write failed");
        double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count();
        std::cout<<"{\"parents_completed\":"<<completed<<",\"start\":"<<start<<",\"end\":"<<end
                 <<",\"records\":"<<records<<",\"nodes\":"<<nodes<<",\"planarity_tests\":"<<tests
                 <<",\"nonplanar_prefixes\":"<<prunes<<",\"raw_extensions_accounted\":"<<covered
                 <<",\"boost_version\":"<<BOOST_VERSION<<",\"threads\":"<<threads
                 <<",\"seconds\":"<<seconds<<"}"<<std::endl;
        return 0;
    } catch(const std::exception& e) {std::cerr<<"FAILED / INCONCLUSIVE: "<<e.what()<<std::endl; return 1;}
}
