#include "TrieformProverK45.h"

bool TrieformProverK45::handledTransitivity = false;

shared_ptr<Trieform>
TrieformFactory::makeTrieK45(const shared_ptr<Formula> &formula,
                             shared_ptr<Trieform> trieParent) {
  shared_ptr<Trieform> trie = shared_ptr<Trieform>(new TrieformProverK45());
  trie->initialise(formula, trieParent);
  return trie;
}
shared_ptr<Trieform>
TrieformFactory::makeTrieK45(const shared_ptr<Formula> &formula,
                             const vector<int> &newModality,
                             shared_ptr<Trieform> trieParent) {
  shared_ptr<Trieform> trie = shared_ptr<Trieform>(new TrieformProverK45());
  trie->initialise(formula, newModality, trieParent);
  return trie;
}
shared_ptr<Trieform>
TrieformFactory::makeTrieK45(const vector<int> &newModality,
                             shared_ptr<Trieform> trieParent) {
  shared_ptr<Trieform> trie = shared_ptr<Trieform>(new TrieformProverK45());
  trie->initialise(newModality, trieParent);
  return trie;
}

TrieformProverK45::TrieformProverK45() {}
TrieformProverK45::~TrieformProverK45() {}

shared_ptr<Trieform>
TrieformProverK45::create(const shared_ptr<Formula> &formula) {
  return TrieformFactory::makeTrieK45(formula, shared_from_this());
}
shared_ptr<Trieform>
TrieformProverK45::create(const shared_ptr<Formula> &formula,
                          const vector<int> &newModality) {
  return TrieformFactory::makeTrieK45(formula, newModality);
}
shared_ptr<Trieform> TrieformProverK45::create(const vector<int> &newModality) {
  return TrieformFactory::makeTrieK45(newModality);
}

void TrieformProverK45::transitiveMakePersistence() {
  for (auto modalSubtrie : subtrieMap) {
    dynamic_cast<TrieformProverK45 *>(modalSubtrie.second.get())
        ->transitiveMakePersistence();
  }

  modal_clause_set persistentBoxes;
  for (ModalClause boxClause : clauses.getBoxClauses()) {
    // For a=>[]b in our box clauses replace with
    // a=>Pb
    // Pb=>[]Pb
    // [](Pb=>b)

    // Make persistence
    shared_ptr<Formula> persistent =
        persistentCache.getVariableOrCreate(boxClause.right);
    persistentBoxes.insert({boxClause.modality, persistent, persistent});

    formula_set leftSet;
    leftSet.insert(Not::create(boxClause.left)->negatedNormalForm());
    leftSet.insert(persistent);
    clauses.addClause(Or::create(leftSet));

    formula_set rightSet;
    rightSet.insert(Not::create(persistent)->negatedNormalForm());
    rightSet.insert(boxClause.right);
    propagateClauses(Box::create(boxClause.modality, 1, Or::create(rightSet)));
  }
  clauses.setBoxClauses(persistentBoxes);

  for (ModalClause persistentBox : persistentBoxes) {
    subtrieMap[persistentBox.modality]->clauses.addBoxClause(persistentBox);
  }
}

void TrieformProverK45::transitivePropagateLevels() {
  for (auto modalSubtrie : subtrieMap) {
    if (modalSubtrie.second->hasSubtrie(modalSubtrie.first)) {
      modalSubtrie.second->getSubtrie(modalSubtrie.first)
          ->overShadow(modalSubtrie.second, modalSubtrie.first);
    }
    dynamic_cast<TrieformProverK45 *>(modalSubtrie.second.get())
        ->transitivePropagateLevels();
  }
}

void TrieformProverK45::preprocessTransitive() {
  transitiveMakePersistence();
  transitivePropagateLevels();
}

void TrieformProverK45::preprocessEuclidean() {
  TrieformProverK5::preprocess();
}

void TrieformProverK45::preprocess() {
  cout << "DOING K45" << endl;
  if (!handledTransitivity) {
    cout << "DOING TRANS :D" << endl;
    preprocessTransitive();
    handledTransitivity = true;
  }
  preprocessEuclidean();
}

Solution TrieformProverK45::prove(vector<shared_ptr<Bitset>> history,
                                  literal_set assumptions) {
  // cout << "SOLVING [";
  // for (int ms : modality) {
  //   cout << ms << ",";
  // }
  // cout << "] WITH ASSUMPS [";
  // for (Literal lit : assumptions) {
  //   cout << lit.toString() << ",";
  // }
  // cout << "]" << endl;

  // Check solution memo
  shared_ptr<Bitset> assumptionsBitset =
      convertAssumptionsToBitset(assumptions);
  LocalSolutionMemoResult memoResult = localMemo.getFromMemo(assumptionsBitset);

  if (memoResult.inSatMemo) {
    // if (memoResult.result.satisfiable) {

    //   cout << "MEMOSAT" << endl;
    // } else {
    //   cout << "MEMOUNSAT" << endl;
    // }
    return memoResult.result;
  }

  if (isInHistory(history, assumptionsBitset)) {
    // cout << "HISTORYSAT" << endl;
    return {true, literal_set()};
  }

  // Solve locally
  Solution solution = prover->solve(assumptions);

  if (!solution.satisfiable) {
    // cout << "UNSAT" << endl;
    updateSolutionMemo(assumptionsBitset, solution);
    return solution;
  }

  prover->calculateTriggeredDiamondsClauses();
  modal_literal_map triggeredDiamonds = prover->getTriggeredDiamondClauses();

  // If there are no fired diamonds, it is satisfiable
  if (triggeredDiamonds.size() == 0) {
    // cout << "NO DIAMONDS SAT" << endl;
    updateSolutionMemo(assumptionsBitset, solution);
    return solution;
  }

  prover->calculateTriggeredBoxClauses();
  modal_literal_map triggeredBoxes = prover->getTriggeredBoxClauses();

  for (auto modalityDiamonds : triggeredDiamonds) {
    // cout << "ITERATING OVER DIAMONDS" << endl;
    // Handle each modality
    if (modalityDiamonds.second.size() == 0) {
      // If there are no triggered diamonds of a certain modality we can skip
      // it
      continue;
    }

    diamond_queue diamondPriority =
        prover->getPrioritisedTriggeredDiamonds(modalityDiamonds.first);
    while (!diamondPriority.empty()) {
      // Create a world for each diamond if necessary
      Literal diamond = diamondPriority.top().literal;
      diamondPriority.pop();

      // If the diamond is already satisfied by reflexivity no need to create
      // a successor.
      if (modality.size() > 0 &&
          modality[modality.size() - 1] == modalityDiamonds.first &&
          prover->modelSatisfiesAssump(diamond)) {
        // cout << "TRIVIALLY SATISFIED BY REFLEXIVITY???" << endl;
        continue;
      }
      // cout << "CHECKING FURTHER" << endl;
      literal_set childAssumptions =
          literal_set(triggeredBoxes[modalityDiamonds.first]);
      childAssumptions.insert(diamond);

      // Run the solver for the next level
      Solution childSolution;
      if (modality.size() > 1 &&
          modality[modality.size() - 1] == modalityDiamonds.first) {
        // cout << "CALLING RECURSIVE" << endl;
        history.push_back(assumptionsBitset);
        childSolution = prove(history, childAssumptions);
        history.pop_back();
      } else {
        // cout << "CALLING DEEPEN" << endl;
        childSolution = dynamic_cast<TrieformProverK45 *>(
                            subtrieMap[modalityDiamonds.first].get())
                            ->prove(childAssumptions);
      }

      // If it is satisfiable create the next world
      if (childSolution.satisfiable) {
        continue;
      }

      // Otherwise there must have been a conflict
      vector<literal_set> badImplications = prover->getNotProblemBoxClauses(
          modalityDiamonds.first, childSolution.conflict);

      if (childSolution.conflict.find(diamond) !=
          childSolution.conflict.end()) {
        // The diamond clause, either on its own or together with box clauses,
        // caused a conflict. We must add diamond implies OR NOT problem box
        // clauses.
        prover->updateLastFail(diamond);
        badImplications.push_back(
            prover->getNotDiamondLeft(modalityDiamonds.first, diamond));

        for (literal_set learnClause : generateClauses(badImplications)) {
          prover->addClause(learnClause);
        }

        // Find new result
        // cout << "RESTART" << endl;
        return prove(history, assumptions);
      } else {
        // Should be able to remove this (boxes must be able to satisfied
        // because of reflexivity)
        // Only the box clauses caused a conflict, so
        // we must add each diamond clause implies OR NOT problem box lefts
        badImplications.push_back(
            prover->getNotAllDiamondLeft(modalityDiamonds.first));
        // Add ~leftDiamond=>\/~leftProbemBox
        for (literal_set learnClause : generateClauses(badImplications)) {
          prover->addClause(learnClause);
        }
        // Find new result
        // cout << "RESTART" << endl;
        return prove(history, assumptions);
      }
    }
  }
  // cout << "Just SAT" << endl;
  // If we reached here the solution is satisfiable under all modalities
  return solution;
}

Solution TrieformProverK45::prove(literal_set assumptions = literal_set()) {
  return prove(vector<shared_ptr<Bitset>>(), assumptions);
}