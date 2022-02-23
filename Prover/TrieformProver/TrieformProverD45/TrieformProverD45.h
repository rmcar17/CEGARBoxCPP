#ifndef TRIEFORM_PROVER_D45
#define TRIEFORM_PROVER_D45

#include "../../../Bitset/Bitset.h"
#include "../../../Clausifier/TrieformFactory/TrieformFactory.h"
#include "../TrieformProverK45/TrieformProverK45.h"
#include <memory>
#include <string>
#include <unordered_map>

using namespace std;

class TrieformProverD45 : public TrieformProverK45 {
protected:
  void ensureSeriality();

public:
  TrieformProverD45();
  ~TrieformProverD45();

  void preprocess();

  shared_ptr<Trieform> create(const shared_ptr<Formula> &formula);
  shared_ptr<Trieform> create(const shared_ptr<Formula> &formula,
                              const vector<int> &newModality);
  shared_ptr<Trieform> create(const vector<int> &newModality);
};

#endif