#ifndef TRIEFORM_PROVER_D5
#define TRIEFORM_PROVER_D5

#include "../../../Bitset/Bitset.h"
#include "../../../Clausifier/TrieformFactory/TrieformFactory.h"
#include "../TrieformProverK5/TrieformProverK5.h"
#include <memory>
#include <string>
#include <unordered_map>

using namespace std;

class TrieformProverD5 : public TrieformProverK5 {
protected:
  void ensureSeriality();

public:
  TrieformProverD5();
  ~TrieformProverD5();

  void preprocess();

  shared_ptr<Trieform> create(const shared_ptr<Formula> &formula);
  shared_ptr<Trieform> create(const shared_ptr<Formula> &formula,
                              const vector<int> &newModality);
  shared_ptr<Trieform> create(const vector<int> &newModality);
};

#endif