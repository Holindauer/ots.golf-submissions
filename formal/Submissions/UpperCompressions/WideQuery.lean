import OptimalOTS.Dag

namespace OptimalOTS.WeightedConstruction.WideForest

abbrev EncInput := Message × BitVec 86

def encQuery (u : EncInput) : Query := ⟨msgBits + 86, u.1 ++ u.2⟩

theorem encQuery_length (u : EncInput) : (encQuery u).1 = 342 := rfl

theorem ne_encQuery_of_length_ne {q : Query} (hq : q.1 ≠ msgBits + 86)
    (u : EncInput) : q ≠ encQuery u := by
  intro h
  exact hq (congrArg Sigma.fst h)

end OptimalOTS.WeightedConstruction.WideForest
