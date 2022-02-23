#include "TrieformProverK5.h"

Cache TrieformProverK5::persistentCache = Cache("P");

shared_ptr<Trieform>
TrieformFactory::makeTrieK5(const shared_ptr<Formula> &formula,
                            shared_ptr<Trieform> trieParent) {
  shared_ptr<Trieform> trie = shared_ptr<Trieform>(new TrieformProverK5());
  trie->initialise(formula, trieParent);
  return trie;
}
shared_ptr<Trieform>
TrieformFactory::makeTrieK5(const shared_ptr<Formula> &formula,
                            const vector<int> &newModality,
                            shared_ptr<Trieform> trieParent) {
  shared_ptr<Trieform> trie = shared_ptr<Trieform>(new TrieformProverK5());
  trie->initialise(formula, newModality, trieParent);
  return trie;
}
shared_ptr<Trieform>
TrieformFactory::makeTrieK5(const vector<int> &newModality,
                            shared_ptr<Trieform> trieParent) {
  shared_ptr<Trieform> trie = shared_ptr<Trieform>(new TrieformProverK5());
  trie->initialise(newModality, trieParent);
  return trie;
}

TrieformProverK5::TrieformProverK5() {}
TrieformProverK5::~TrieformProverK5() {}

shared_ptr<Trieform>
TrieformProverK5::create(const shared_ptr<Formula> &formula) {
  return TrieformFactory::makeTrieK5(formula, shared_from_this());
}
shared_ptr<Trieform>
TrieformProverK5::create(const shared_ptr<Formula> &formula,
                         const vector<int> &newModality) {
  return TrieformFactory::makeTrieK5(formula, newModality);
}
shared_ptr<Trieform> TrieformProverK5::create(const vector<int> &newModality) {
  return TrieformFactory::makeTrieK5(newModality);
}
bool TrieformProverK5::isInHistory(vector<shared_ptr<Bitset>> history,
                                   shared_ptr<Bitset> bitset) {
  for (shared_ptr<Bitset> assump : history) {
    if (assump->contains(*bitset)) {
      return true;
    }
  }
  return false;
}

shared_ptr<Bitset>
TrieformProverK5::convertAssumptionsToBitset(literal_set literals) {
  shared_ptr<Bitset> bitset =
      shared_ptr<Bitset>(new Bitset(2 * assumptionsSize));
  for (Literal literal : literals) {
    bitset->set(2 * idMap[literal.getName()] + literal.getPolarity());
  }
  return bitset;
}

void TrieformProverK5::updateSolutionMemo(const shared_ptr<Bitset> &assumptions,
                                          Solution solution) {
  if (solution.satisfiable) {
    localMemo.insertSat(assumptions);
  } else {
    localMemo.insertUnsat(assumptions, solution.conflict);
  }
}

void TrieformProverK5::propagateEuclideaness() {
  for (const ModalClause &clause : clauses.getDiamondClauses()) {
    if (modality.size() == 0 ||
        clause.modality != modality[modality.size() - 1]) {
      formula_set newOr;
      newOr.insert(clause.left->negate());
      if (cache.inverseContains(clause.right)) {
        newOr.insert(Box::create(
            clause.modality, 1,
            Diamond::create(clause.modality, 1,
                            cache.getInverseFormula(clause.right))));
      } else {
        newOr.insert(
            Box::create(clause.modality, 1,
                        Diamond::create(clause.modality, 1, clause.right)));
      }

      propagateClauses(Or::create(newOr));
    }
  }
}

void TrieformProverK5::reflexiveHandleBoxClauses() {
  for (ModalClause modalClause : clauses.getBoxClauses()) {
    if (modalClause.modality == modality[modality.size() - 1]) {
      formula_set newOr;
      newOr.insert(Not::create(modalClause.left)->negatedNormalForm());
      newOr.insert(modalClause.right);
      clauses.addClause(Or::create(newOr));
    }
  }

  if (hasSubtrie(modality[modality.size() - 1])) {
    dynamic_cast<TrieformProverK5 *>(
        getSubtrie(modality[modality.size() - 1]).get())
        ->reflexiveHandleBoxClauses();
  }
}

void TrieformProverK5::reflexivepropagateLevels() {
  if (hasSubtrie(modality[modality.size() - 1])) {
    shared_ptr<TrieformProverK5> subtrie =
        dynamic_pointer_cast<TrieformProverK5>(
            getSubtrie(modality[modality.size() - 1]));
    subtrie->reflexivepropagateLevels();
    overShadow(subtrie, modality[modality.size() - 1]);
  }
}

void TrieformProverK5::pruneTrie() {
  if (hasSubtrie(modality[modality.size() - 1])) {
    TrieformProverK5 *subtrie = dynamic_cast<TrieformProverK5 *>(
        getSubtrie(modality[modality.size() - 1]).get());
    if (subtrie->hasSubtrie(modality[modality.size() - 1])) {
      subtrie->removeSubtrie(modality[modality.size() - 1]);
    }
  }
}

void TrieformProverK5::makePersistence() {
  if (hasSubtrie(modality[modality.size() - 1])) {
    dynamic_cast<TrieformProverK5 *>(
        getSubtrie(modality[modality.size() - 1]).get())
        ->makePersistence();
  }

  modal_clause_set persistentBoxes;
  for (ModalClause boxClause : clauses.getBoxClauses()) {
    if (boxClause.modality == modality[modality.size() - 1]) {
      // For a=>[]b in our box clauses replace with.
      // a=>Pb
      // Pb=>[]Pb
      // [](Pb=>b)

      // Make persistence (Pb=>[]Pb). Don't need to add Pb=>Pb

      shared_ptr<Formula> persistent =
          persistentCache.getVariableOrCreate(boxClause.right);
      persistentBoxes.insert({boxClause.modality, persistent, persistent});
      persistentBoxes.insert(
          {boxClause.modality, persistent->negate(), persistent->negate()});

      // Add a=>Pb
      formula_set leftSet;
      leftSet.insert(Not::create(boxClause.left)->negatedNormalForm());
      leftSet.insert(persistent);
      clauses.addClause(Or::create(leftSet));

      // Add b=>Pb and [](b=>Pb) where appropriate
      formula_set rightSet;
      rightSet.insert(Not::create(persistent)->negatedNormalForm());
      rightSet.insert(boxClause.right);
      shared_ptr<Formula> rightOr = Or::create(rightSet);
      propagateClauses(rightOr);
      if (modality.size() == 1 ||
          (modality.size() > 1 &&
           modality[modality.size() - 1] != modality[modality.size() - 2])) {
        getSubtrieOrEmpty(boxClause.modality)->propagateClauses(rightOr);
      }
    } else {
      persistentBoxes.insert(boxClause);
    }
  }
  clauses.setBoxClauses(persistentBoxes);

  for (ModalClause persistentBox : persistentBoxes) {
    if (persistentBox.modality == modality[modality.size() - 1] &&
        (modality.size() == 1 ||
         (modality.size() > 1 &&
          modality[modality.size() - 1] != modality[modality.size() - 2]))) {
      getSubtrieOrEmpty(persistentBox.modality)
          ->clauses.addBoxClause(persistentBox);
    }
  }
}

void TrieformProverK5::preprocess() {
  propagateEuclideaness();

  if (modality.size() == 1 ||
      (modality.size() > 1 &&
       modality[modality.size() - 1] != modality[modality.size() - 2])) {
    reflexiveHandleBoxClauses();
    reflexivepropagateLevels();

    pruneTrie();

    makePersistence();
  }

  for (auto modalSubtrie : subtrieMap) {
    modalSubtrie.second->preprocess();
  }
}

void TrieformProverK5::prepareSAT(name_set extra) {
  for (string name : extra) {
    idMap[name] = assumptionsSize++;
  }
  modal_names_map modalExtras = prover->prepareSAT(clauses, extra);
  for (auto modalSubtrie : subtrieMap) {
    modalSubtrie.second->prepareSAT(modalExtras[modalSubtrie.first]);
  }
}

Solution TrieformProverK5::prove(vector<shared_ptr<Bitset>> history,
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
          modality[modality.size() - 1] == modalityDiamonds.first &&
          modality[modality.size() - 1] == modality[modality.size() - 2]) {
        // cout << "CALLING RECURSIVE" << endl;
        history.push_back(assumptionsBitset);
        childSolution = prove(history, childAssumptions);
        history.pop_back();
      } else {
        // cout << "CALLING DEEPEN" << endl;
        childSolution = dynamic_cast<TrieformProverK5 *>(
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

Solution TrieformProverK5::prove(literal_set assumptions = literal_set()) {
  return prove(vector<shared_ptr<Bitset>>(), assumptions);
}