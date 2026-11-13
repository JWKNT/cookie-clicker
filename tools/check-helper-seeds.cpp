#include <array>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <mutex>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

// Explicit short-ASCII seedrandom path in pinned main.js:702. This is an
// exhaustive native diagnostic, not a Lean theorem or a policy RNG override.
class Arc4 {
  std::array<unsigned, 256> state{};
  unsigned i = 0, j = 0;
 public:
  explicit Arc4(const std::string& seed) {
    if (seed.empty() || seed.size() > 255) throw std::runtime_error("short ASCII seed required");
    for (unsigned n = 0; n < 256; ++n) state[n] = n;
    unsigned shuffle = 0;
    for (unsigned n = 0; n < 256; ++n) {
      const unsigned previous = state[n];
      shuffle = (shuffle + static_cast<unsigned char>(seed[n % seed.size()]) + previous) & 255;
      state[n] = state[shuffle]; state[shuffle] = previous;
    }
    for (unsigned n = 0; n < 256; ++n) byte();
  }
  unsigned byte() {
    i = (i + 1) & 255;
    const unsigned previous = state[i];
    j = (j + previous) & 255;
    state[i] = state[j]; state[j] = previous;
    return state[(state[i] + state[j]) & 255];
  }
  double next() {
    double numerator = 0;
    for (unsigned n = 0; n < 6; ++n) numerator = numerator * 256 + byte();
    double denominator = 281474976710656.0; // 256^6
    unsigned extra = 0;
    while (numerator < 4503599627370496.0) {
      numerator = (numerator + extra) * 256;
      denominator *= 256;
      extra = byte();
    }
    while (numerator >= 9007199254740992.0) {
      numerator /= 2; denominator /= 2; extra >>= 1;
    }
    return (numerator + extra) / denominator;
  }
};

std::string startup_seed(std::uint32_t ordinal) {
  std::string seed(5, 'a');
  for (int i = 4; i >= 0; --i) { seed[i] += ordinal % 26; ordinal /= 26; }
  return seed;
}

std::array<double, 3> sprite_draws(const std::string& seed, unsigned index) {
  Arc4 random(seed + " 1 " + std::to_string(index));
  return {random.next(), random.next(), random.next()};
}

unsigned third_leading_byte(const std::string& seed, unsigned index) {
  Arc4 random(seed + " 1 " + std::to_string(index));
  random.next(); random.next();
  return random.byte();
}

int main(int argc, char** argv) {
  try {
    if (argc == 3 && std::string(argv[1]) == "--samples") {
      std::ifstream input(argv[2]);
      if (!input) throw std::runtime_error("cannot read sample file");
      std::string seed; unsigned index;
      std::cout << std::setprecision(17);
      while (input >> seed >> index) {
        const auto draws = sprite_draws(seed, index);
        std::cout << seed << ' ' << index;
        for (const double value : draws) {
          std::uint64_t bits; std::memcpy(&bits, &value, sizeof(bits));
          std::cout << ' ' << std::hex << std::setfill('0') << std::setw(16) << bits << std::dec;
        }
        std::cout << '\n';
      }
      return 0;
    }
    const bool verify = argc >= 2 && std::string(argv[1]) == "--verify";
    if (argc < 4 || argc > 6 || (!verify && std::string(argv[1]) != "--scan"))
      throw std::runtime_error("usage: check-helper-seeds --samples FILE | --scan CERTIFICATE SUMMARY [COUNT] [THREADS] | --verify CERTIFICATE SUMMARY [COUNT] [THREADS]");
    constexpr std::uint32_t domain = 11881376;
    const std::uint32_t count = argc >= 5 ? std::stoul(argv[4]) : domain;
    const unsigned threads = argc >= 6 ? std::stoul(argv[5]) : 4;
    if (count == 0 || count > domain || threads == 0 || threads > 64) throw std::runtime_error("invalid count or thread count");
    std::vector<unsigned char> certificate(count, 255);
    if (verify) {
      std::ifstream binary(argv[2], std::ios::binary);
      binary.read(reinterpret_cast<char*>(certificate.data()), certificate.size());
      if (binary.gcount() != count || binary.peek() != EOF) throw std::runtime_error("certificate size differs from count");
    }
    std::atomic<std::uint32_t> next{0}, done{0}, report{1000000};
    std::mutex output;
    const auto start = std::chrono::steady_clock::now();
    const auto elapsed = [&]() { return std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count(); };
    const auto work = [&]() {
      while (true) {
        const std::uint32_t begin = next.fetch_add(1024);
        if (begin >= count) break;
        const std::uint32_t end = std::min(count, begin + 1024);
        for (std::uint32_t ordinal = begin; ordinal < end; ++ordinal) {
          const std::string seed = startup_seed(ordinal);
          if (verify) {
            if (certificate[ordinal] == 255 || third_leading_byte(seed, certificate[ordinal]) < 128) certificate[ordinal] = 255;
          } else for (unsigned index = 0; index < 255; ++index)
            if (sprite_draws(seed, index)[2] >= 0.5) { certificate[ordinal] = index; break; }
        }
        const std::uint32_t completed = done.fetch_add(end - begin) + end - begin;
        unsigned threshold = report.load();
        if (completed >= threshold && report.compare_exchange_strong(threshold, threshold + 1000000)) {
          std::lock_guard<std::mutex> lock(output);
          std::cerr << "checked " << completed << '/' << count << " seeds in " << elapsed() << " seconds\n";
        }
      }
    };
    std::vector<std::thread> workers;
    for (unsigned n = 0; n < threads; ++n) workers.emplace_back(work);
    for (auto& worker : workers) worker.join();
    const double seconds = elapsed();
    std::array<std::uint32_t, 256> histogram{};
    unsigned maximum = 0;
    std::uint32_t maximumOrdinal = 0;
    for (std::uint32_t ordinal = 0; ordinal < count; ++ordinal) {
      const unsigned index = certificate[ordinal]; histogram[index]++;
      if (index > maximum) { maximum = index; maximumOrdinal = ordinal; }
    }
    if (!verify) {
      std::ofstream binary(argv[2], std::ios::binary);
      binary.write(reinterpret_cast<const char*>(certificate.data()), certificate.size());
      if (!binary) throw std::runtime_error("cannot write certificate");
    }
    std::ofstream summary(argv[3]);
    summary << std::setprecision(17) << "{\n  \"schemaVersion\": 1,\n  \"scope\": \"native-exhaustive-enumeration-not-Lean-proof\",\n"
      << "  \"domainSize\": " << domain << ",\n  \"checkedSeeds\": " << count
      << ",\n  \"allStartupSeedsCovered\": " << (count == domain ? "true" : "false")
      << ",\n  \"unresolvedSeeds\": " << histogram[255]
      << ",\n  \"maximumFirstHelperIndex\": " << maximum
      << ",\n  \"firstMaximumSeed\": \"" << startup_seed(maximumOrdinal) << "\",\n"
      << "  \"certificateEncoding\": \"one unsigned byte per five-letter lowercase seed in lexicographic order; first helper index; 255 means unresolved\",\n"
      << "  \"artworkList\": [\"grandma.png\", \"elfGrandma.png\"],\n"
      << "  \"predicate\": \"third native-style seedrandom draw for seed + ' 1 ' + index is >= 0.5\",\n"
      << "  \"allChosenThirdLeadingBytesAtLeast128\": " << (verify && histogram[255] == 0 ? "true" : "false") << ",\n"
      << "  \"threads\": " << threads << ",\n  \"elapsedSeconds\": " << seconds << ",\n  \"histogram\": [";
    for (unsigned index = 0; index <= maximum; ++index) { if (index) summary << ','; summary << histogram[index]; }
    summary << "]\n}\n";
    if (!summary) throw std::runtime_error("cannot write summary");
    std::cout << "checked " << count << " seeds; maximum first helper index " << maximum
      << "; unresolved " << histogram[255] << "; elapsed " << seconds << " seconds\n";
    return histogram[255] == 0 ? 0 : 1;
  } catch (const std::exception& error) { std::cerr << error.what() << '\n'; return 2; }
}
