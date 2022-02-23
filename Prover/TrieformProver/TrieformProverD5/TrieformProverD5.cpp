#include "TrieformProverD5.h"

shared_ptr<Trieform>
TrieformFactory::makeTrieD5(const shared_ptr<Formula> &formula,
                            shared_ptr<Trieform> trieParent) {
  shared_ptr<Trieform> trie = shared_ptr<Trieform>(new TrieformProverD5());
  trie->initialise(formula, trieParent);
  return trie;
}
shared_ptr<Trieform>
TrieformFactory::makeTrieD5(const shared_ptr<Formula> &formula,
                            const vector<int> &newModality,
                            shared_ptr<Trieform> trieParent) {
  shared_ptr<Trieform> trie = shared_ptr<Trieform>(new TrieformProverD5());
  trie->initialise(formula, newModality, trieParent);
  return trie;
}
shared_ptr<Trieform>
TrieformFactory::makeTrieD5(const vector<int> &newModality,
                            shared_ptr<Trieform> trieParent) {
  shared_ptr<Trieform> trie = shared_ptr<Trieform>(new TrieformProverD5());
  trie->initialise(newModality, trieParent);
  return trie;
}

TrieformProverD5::TrieformProverD5() {}
TrieformProverD5::~TrieformProverD5() {}

shared_ptr<Trieform>
TrieformProverD5::create(const shared_ptr<Formula> &formula) {
  return TrieformFactory::makeTrieD5(formula, shared_from_this());
}
shared_ptr<Trieform>
TrieformProverD5::create(const shared_ptr<Formula> &formula,
                         const vector<int> &newModality) {
  return TrieformFactory::makeTrieD5(formula, newModality);
}
shared_ptr<Trieform> TrieformProverD5::create(const vector<int> &newModality) {
  return TrieformFactory::makeTrieD5(newModality);
}

void TrieformProverD5::preprocess() {
  TrieformProverK5::preprocess();

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
