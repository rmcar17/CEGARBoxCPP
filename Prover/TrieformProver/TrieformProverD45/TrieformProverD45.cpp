#include "TrieformProverD45.h"

shared_ptr<Trieform>
TrieformFactory::makeTrieD45(const shared_ptr<Formula> &formula,
                             shared_ptr<Trieform> trieParent) {
  shared_ptr<Trieform> trie = shared_ptr<Trieform>(new TrieformProverD45());
  trie->initialise(formula, trieParent);
  return trie;
}
shared_ptr<Trieform>
TrieformFactory::makeTrieD45(const shared_ptr<Formula> &formula,
                             const vector<int> &newModality,
                             shared_ptr<Trieform> trieParent) {
  shared_ptr<Trieform> trie = shared_ptr<Trieform>(new TrieformProverD45());
  trie->initialise(formula, newModality, trieParent);
  return trie;
}
shared_ptr<Trieform>
TrieformFactory::makeTrieD45(const vector<int> &newModality,
                             shared_ptr<Trieform> trieParent) {
  shared_ptr<Trieform> trie = shared_ptr<Trieform>(new TrieformProverD45());
  trie->initialise(newModality, trieParent);
  return trie;
}

TrieformProverD45::TrieformProverD45() {}
TrieformProverD45::~TrieformProverD45() {}

shared_ptr<Trieform>
TrieformProverD45::create(const shared_ptr<Formula> &formula) {
  return TrieformFactory::makeTrieD45(formula, shared_from_this());
}
shared_ptr<Trieform>
TrieformProverD45::create(const shared_ptr<Formula> &formula,
                          const vector<int> &newModality) {
  return TrieformFactory::makeTrieD45(formula, newModality);
}
shared_ptr<Trieform> TrieformProverD45::create(const vector<int> &newModality) {
  return TrieformFactory::makeTrieD45(newModality);
}

void TrieformProverD45::preprocess() {
  cout << "CALLING K45?" << endl;
  TrieformProverK45::preprocess();
  cout << "DONE CALLING" << endl;

  bool foundTransitive = modality.size() == 0;
  int transitiveMod = 0;
  if (modality.size() > 0) {
    transitiveMod = modality[modality.size() - 1];
  }
  for (int mod : futureModalities) {
    if (!foundTransitive && transitiveMod == mod) {
      foundTransitive = true;
    }
    clauses.addDiamondClause({mod, True::create(), True::create()});
  }
  if (!foundTransitive) {
    clauses.addDiamondClause({transitiveMod, True::create(), True::create()});
  }
}
