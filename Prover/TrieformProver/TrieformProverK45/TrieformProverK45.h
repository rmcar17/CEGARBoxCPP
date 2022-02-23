#ifndef TRIEFORM_PROVER_K45
#define TRIEFORM_PROVER_K45

#include "../../../Bitset/Bitset.h"
#include "../../../Clausifier/TrieformFactory/TrieformFactory.h"
#include "../TrieformProverK5/TrieformProverK5.h"
#include <memory>
#include <string>
#include <unordered_map>

using namespace std;

class TrieformProverK45 : public TrieformProverK5 {
protected:
  static bool handledTransitivity;
  void preprocessEuclidean();
  void preprocessTransitive();

  void transitiveMakePersistence();
  void transitivePropagateLevels();

public:
  TrieformProverK45();
  ~TrieformProverK45();

  void preprocess();

  shared_ptr<Trieform> create(const shared_ptr<Formula> &formula);
  shared_ptr<Trieform> create(const shared_ptr<Formula> &formula,
                              const vector<int> &newModality);
  shared_ptr<Trieform> create(const vector<int> &newModality);

  Solution prove(vector<shared_ptr<Bitset>> history, literal_set assumptions);
  virtual Solution prove(literal_set assumptions);
};

#endif