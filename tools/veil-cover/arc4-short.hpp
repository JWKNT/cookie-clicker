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

