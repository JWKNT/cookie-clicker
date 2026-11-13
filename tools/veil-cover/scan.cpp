#include "arc4-short.hpp"
int main(int argc,char**argv){
 try{
  if(argc==3&&std::string(argv[1])=="--samples"){
   std::ifstream in(argv[2]);std::string seed;unsigned count;
   while(in>>seed>>count){Arc4 r(seed+"/"+std::to_string(count));std::uint64_t word=0;for(int k=0;k<6;k++)word=word*256+r.byte();Arc4 actual(seed+"/"+std::to_string(count));double value=actual.next();std::uint64_t bits;std::memcpy(&bits,&value,8);std::cout<<seed<<' '<<count<<' '<<word<<' '<<std::hex<<std::setfill('0')<<std::setw(16)<<bits<<std::dec<<'\n';}
   return 0;
  }
  if(argc<4||argc>6)throw std::runtime_error("scan CERT SUMMARY COUNT [THREADS] [BOUND]");
  const auto count=std::stoul(argv[3]);const unsigned threads=argc>4?std::stoul(argv[4]):2,bound=argc>5?std::stoul(argv[5]):64;
  if(count>11881376||count==0||threads==0||bound>254||bound==0)throw std::runtime_error("bad limits");
  std::vector<unsigned char> cert(count,255);std::atomic<unsigned> next{0},done{0},report{1000000},zeroWords{0};
  const auto begin=std::chrono::steady_clock::now();const auto seconds=[&]{return std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count();};std::mutex output;
  const auto work=[&]{while(true){const auto lo=next.fetch_add(1024);if(lo>=count)break;const auto hi=std::min<unsigned long>(count,lo+1024);
   for(unsigned ordinal=lo;ordinal<hi;ordinal++){const auto seed=startup_seed(ordinal);for(unsigned k=0;k<bound;k++){
    Arc4 r(seed+"/"+std::to_string(k));std::uint64_t word=0;for(int i=0;i<6;i++)word=word*256+r.byte();
    if(word==0)zeroWords++;
    const unsigned leading=word>>40;
    if(leading>=1&&leading<=101){cert[ordinal]=k;break;}
   }}
   const unsigned completed=done.fetch_add(hi-lo)+hi-lo;unsigned threshold=report.load();if(completed>=threshold&&report.compare_exchange_strong(threshold,threshold+1000000)){std::lock_guard<std::mutex>lock(output);std::cerr<<completed<<'/'<<count<<" seeds; "<<seconds()<<" seconds\n";}
  }};
  std::vector<std::thread>workers;for(unsigned k=0;k<threads;k++)workers.emplace_back(work);for(auto&w:workers)w.join();
  std::array<unsigned,256>hist{};unsigned maximum=0,worst=0;for(unsigned ordinal=0;ordinal<count;ordinal++){hist[cert[ordinal]]++;if(cert[ordinal]>maximum){maximum=cert[ordinal];worst=ordinal;}}
  std::ofstream bin(argv[1],std::ios::binary);bin.write(reinterpret_cast<const char*>(cert.data()),cert.size());
  std::ofstream out(argv[2]);out<<std::setprecision(17)<<"{\"scope\":\"exhaustive native-integer certificate; not a Lean proof\",\"count\":"<<count<<",\"allSeeds\":"<<(count==11881376?"true":"false")<<",\"counterBoundExclusive\":"<<bound<<",\"unresolved\":"<<hist[255]<<",\"maxSufficientCounter\":"<<maximum<<",\"firstWorstSeed\":\""<<startup_seed(worst)<<"\",\"zeroInitialSixByteWordsThroughSelectedCounter\":"<<zeroWords.load()<<",\"predicate\":\"ARC4(seed+'/'+counter) after256 discarded bytes has first output byte in1..101\",\"elapsedSeconds\":"<<seconds()<<",\"histogram\":[";
  for(unsigned i=0;i<=maximum;i++){if(i)out<<',';out<<hist[i];}out<<"]}\n";
  std::cout<<"checked "<<count<<" seeds; max counter "<<maximum<<"; unresolved "<<hist[255]<<"; zero words "<<zeroWords.load()<<"; seconds "<<seconds()<<'\n';
  return hist[255]==0&&zeroWords==0?0:1;
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 2;}
}
