import FvdepLedger.Types

/-! Contract-only fixture: DeepStatement. Each checker invocation loads this module alone. -/

namespace FvdepLedgerFixtures.DeepStatement

set_option maxRecDepth 4096

def deepTail : Nat := 314159

def plan (args : List String) : Nat := args.length

def interpret (value : Nat) : Nat := value

def main (args : List String) : Nat := interpret (plan args)

def statement : Prop :=
  ∀ args : List String,
    plan args = args.length ∧
      (True ∧
        (True ∧
          (True ∧
            (True ∧
              (True ∧
                (True ∧
                  (True ∧
                    (True ∧
                      (True ∧
                        (True ∧
                          (True ∧
                            (True ∧
                              (True ∧
                                (True ∧
                                  (True ∧
                                    (True ∧
                                      (True ∧
                                        (True ∧
                                          (True ∧
                                            (True ∧
                                              (True ∧
                                                (True ∧
                                                  (True ∧
                                                    (True ∧
                                                      (True ∧
                                                        (True ∧
                                                          (True ∧
                                                            (True ∧
                                                              (True ∧
                                                                (True ∧
                                                                  (True ∧
                                                                    (True ∧
                                                                      (True ∧
                                                                        (True ∧
                                                                          (True ∧
                                                                            (True ∧
                                                                              (True ∧
                                                                                (True ∧
                                                                                  (True ∧
                                                                                    (True ∧
                                                                                      (True ∧
                                                                                        (True ∧
                                                                                          (True ∧
                                                                                            (True ∧
                                                                                              (True ∧
                                                                                                (True ∧
                                                                                                  (True ∧
                                                                                                    (True ∧
                                                                                                      (True ∧
                                                                                                        (True ∧
                                                                                                          (True ∧
                                                                                                            (True ∧
                                                                                                              (True ∧
                                                                                                                (True ∧
                                                                                                                  (True ∧
                                                                                                                    (True ∧
                                                                                                                      (True ∧
                                                                                                                        (True ∧
                                                                                                                          (True ∧
                                                                                                                            (True ∧
                                                                                                                              (True ∧
                                                                                                                                (True ∧
                                                                                                                                  (True ∧
                                                                                                                                    (True ∧
                                                                                                                                      (True ∧
                                                                                                                                        (True ∧
                                                                                                                                          (True ∧
                                                                                                                                            (True ∧
                                                                                                                                              (True ∧
                                                                                                                                                (True ∧
                                                                                                                                                  (True ∧
                                                                                                                                                    (True ∧
                                                                                                                                                      (True ∧
                                                                                                                                                        (True ∧
                                                                                                                                                          (True ∧
                                                                                                                                                            (True ∧
                                                                                                                                                              (True ∧
                                                                                                                                                                (True ∧
                                                                                                                                                                  (True ∧
                                                                                                                                                                    (True ∧
                                                                                                                                                                      (True ∧
                                                                                                                                                                        (True ∧
                                                                                                                                                                          (True ∧
                                                                                                                                                                            (True ∧
                                                                                                                                                                              (True ∧
                                                                                                                                                                                (True ∧
                                                                                                                                                                                  (True ∧
                                                                                                                                                                                    (True ∧
                                                                                                                                                                                      (True ∧
                                                                                                                                                                                        (True ∧
                                                                                                                                                                                          (True ∧
                                                                                                                                                                                            (True ∧
                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                                                                                                                                      (deepTail =
                                                                                                                                                                                                                                                                                                                                        deepTail)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem proof :
    ∀ args : List String,
      plan args = args.length ∧
        (True ∧
          (True ∧
            (True ∧
              (True ∧
                (True ∧
                  (True ∧
                    (True ∧
                      (True ∧
                        (True ∧
                          (True ∧
                            (True ∧
                              (True ∧
                                (True ∧
                                  (True ∧
                                    (True ∧
                                      (True ∧
                                        (True ∧
                                          (True ∧
                                            (True ∧
                                              (True ∧
                                                (True ∧
                                                  (True ∧
                                                    (True ∧
                                                      (True ∧
                                                        (True ∧
                                                          (True ∧
                                                            (True ∧
                                                              (True ∧
                                                                (True ∧
                                                                  (True ∧
                                                                    (True ∧
                                                                      (True ∧
                                                                        (True ∧
                                                                          (True ∧
                                                                            (True ∧
                                                                              (True ∧
                                                                                (True ∧
                                                                                  (True ∧
                                                                                    (True ∧
                                                                                      (True ∧
                                                                                        (True ∧
                                                                                          (True ∧
                                                                                            (True ∧
                                                                                              (True ∧
                                                                                                (True ∧
                                                                                                  (True ∧
                                                                                                    (True ∧
                                                                                                      (True ∧
                                                                                                        (True ∧
                                                                                                          (True ∧
                                                                                                            (True ∧
                                                                                                              (True ∧
                                                                                                                (True ∧
                                                                                                                  (True ∧
                                                                                                                    (True ∧
                                                                                                                      (True ∧
                                                                                                                        (True ∧
                                                                                                                          (True ∧
                                                                                                                            (True ∧
                                                                                                                              (True ∧
                                                                                                                                (True ∧
                                                                                                                                  (True ∧
                                                                                                                                    (True ∧
                                                                                                                                      (True ∧
                                                                                                                                        (True ∧
                                                                                                                                          (True ∧
                                                                                                                                            (True ∧
                                                                                                                                              (True ∧
                                                                                                                                                (True ∧
                                                                                                                                                  (True ∧
                                                                                                                                                    (True ∧
                                                                                                                                                      (True ∧
                                                                                                                                                        (True ∧
                                                                                                                                                          (True ∧
                                                                                                                                                            (True ∧
                                                                                                                                                              (True ∧
                                                                                                                                                                (True ∧
                                                                                                                                                                  (True ∧
                                                                                                                                                                    (True ∧
                                                                                                                                                                      (True ∧
                                                                                                                                                                        (True ∧
                                                                                                                                                                          (True ∧
                                                                                                                                                                            (True ∧
                                                                                                                                                                              (True ∧
                                                                                                                                                                                (True ∧
                                                                                                                                                                                  (True ∧
                                                                                                                                                                                    (True ∧
                                                                                                                                                                                      (True ∧
                                                                                                                                                                                        (True ∧
                                                                                                                                                                                          (True ∧
                                                                                                                                                                                            (True ∧
                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                                                                                                                                        (True ∧
                                                                                                                                                                                                                                                                                                                          (True ∧
                                                                                                                                                                                                                                                                                                                            (True ∧
                                                                                                                                                                                                                                                                                                                              (True ∧
                                                                                                                                                                                                                                                                                                                                (True ∧
                                                                                                                                                                                                                                                                                                                                  (True ∧
                                                                                                                                                                                                                                                                                                                                    (True ∧
                                                                                                                                                                                                                                                                                                                                      (True ∧
                                                                                                                                                                                                                                                                                                                                        (deepTail =
                                                                                                                                                                                                                                                                                                                                          deepTail))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  intro args
  exact
    And.intro rfl
      (And.intro True.intro
        (And.intro True.intro
          (And.intro True.intro
            (And.intro True.intro
              (And.intro True.intro
                (And.intro True.intro
                  (And.intro True.intro
                    (And.intro True.intro
                      (And.intro True.intro
                        (And.intro True.intro
                          (And.intro True.intro
                            (And.intro True.intro
                              (And.intro True.intro
                                (And.intro True.intro
                                  (And.intro True.intro
                                    (And.intro True.intro
                                      (And.intro True.intro
                                        (And.intro True.intro
                                          (And.intro True.intro
                                            (And.intro True.intro
                                              (And.intro True.intro
                                                (And.intro True.intro
                                                  (And.intro True.intro
                                                    (And.intro True.intro
                                                      (And.intro True.intro
                                                        (And.intro True.intro
                                                          (And.intro True.intro
                                                            (And.intro True.intro
                                                              (And.intro True.intro
                                                                (And.intro True.intro
                                                                  (And.intro True.intro
                                                                    (And.intro True.intro
                                                                      (And.intro True.intro
                                                                        (And.intro True.intro
                                                                          (And.intro True.intro
                                                                            (And.intro True.intro
                                                                              (And.intro True.intro
                                                                                (And.intro
                                                                                  True.intro
                                                                                  (And.intro
                                                                                    True.intro
                                                                                    (And.intro
                                                                                      True.intro
                                                                                      (And.intro
                                                                                        True.intro
                                                                                        (And.intro
                                                                                          True.intro
                                                                                          (And.intro
                                                                                            True.intro
                                                                                            (And.intro
                                                                                              True.intro
                                                                                              (And.intro
                                                                                                True.intro
                                                                                                (And.intro
                                                                                                  True.intro
                                                                                                  (And.intro
                                                                                                    True.intro
                                                                                                    (And.intro
                                                                                                      True.intro
                                                                                                      (And.intro
                                                                                                        True.intro
                                                                                                        (And.intro
                                                                                                          True.intro
                                                                                                          (And.intro
                                                                                                            True.intro
                                                                                                            (And.intro
                                                                                                              True.intro
                                                                                                              (And.intro
                                                                                                                True.intro
                                                                                                                (And.intro
                                                                                                                  True.intro
                                                                                                                  (And.intro
                                                                                                                    True.intro
                                                                                                                    (And.intro
                                                                                                                      True.intro
                                                                                                                      (And.intro
                                                                                                                        True.intro
                                                                                                                        (And.intro
                                                                                                                          True.intro
                                                                                                                          (And.intro
                                                                                                                            True.intro
                                                                                                                            (And.intro
                                                                                                                              True.intro
                                                                                                                              (And.intro
                                                                                                                                True.intro
                                                                                                                                (And.intro
                                                                                                                                  True.intro
                                                                                                                                  (And.intro
                                                                                                                                    True.intro
                                                                                                                                    (And.intro
                                                                                                                                      True.intro
                                                                                                                                      (And.intro
                                                                                                                                        True.intro
                                                                                                                                        (And.intro
                                                                                                                                          True.intro
                                                                                                                                          (And.intro
                                                                                                                                            True.intro
                                                                                                                                            (And.intro
                                                                                                                                              True.intro
                                                                                                                                              (And.intro
                                                                                                                                                True.intro
                                                                                                                                                (And.intro
                                                                                                                                                  True.intro
                                                                                                                                                  (And.intro
                                                                                                                                                    True.intro
                                                                                                                                                    (And.intro
                                                                                                                                                      True.intro
                                                                                                                                                      (And.intro
                                                                                                                                                        True.intro
                                                                                                                                                        (And.intro
                                                                                                                                                          True.intro
                                                                                                                                                          (And.intro
                                                                                                                                                            True.intro
                                                                                                                                                            (And.intro
                                                                                                                                                              True.intro
                                                                                                                                                              (And.intro
                                                                                                                                                                True.intro
                                                                                                                                                                (And.intro
                                                                                                                                                                  True.intro
                                                                                                                                                                  (And.intro
                                                                                                                                                                    True.intro
                                                                                                                                                                    (And.intro
                                                                                                                                                                      True.intro
                                                                                                                                                                      (And.intro
                                                                                                                                                                        True.intro
                                                                                                                                                                        (And.intro
                                                                                                                                                                          True.intro
                                                                                                                                                                          (And.intro
                                                                                                                                                                            True.intro
                                                                                                                                                                            (And.intro
                                                                                                                                                                              True.intro
                                                                                                                                                                              (And.intro
                                                                                                                                                                                True.intro
                                                                                                                                                                                (And.intro
                                                                                                                                                                                  True.intro
                                                                                                                                                                                  (And.intro
                                                                                                                                                                                    True.intro
                                                                                                                                                                                    (And.intro
                                                                                                                                                                                      True.intro
                                                                                                                                                                                      (And.intro
                                                                                                                                                                                        True.intro
                                                                                                                                                                                        (And.intro
                                                                                                                                                                                          True.intro
                                                                                                                                                                                          (And.intro
                                                                                                                                                                                            True.intro
                                                                                                                                                                                            (And.intro
                                                                                                                                                                                              True.intro
                                                                                                                                                                                              (And.intro
                                                                                                                                                                                                True.intro
                                                                                                                                                                                                (And.intro
                                                                                                                                                                                                  True.intro
                                                                                                                                                                                                  (And.intro
                                                                                                                                                                                                    True.intro
                                                                                                                                                                                                    (And.intro
                                                                                                                                                                                                      True.intro
                                                                                                                                                                                                      (And.intro
                                                                                                                                                                                                        True.intro
                                                                                                                                                                                                        (And.intro
                                                                                                                                                                                                          True.intro
                                                                                                                                                                                                          (And.intro
                                                                                                                                                                                                            True.intro
                                                                                                                                                                                                            (And.intro
                                                                                                                                                                                                              True.intro
                                                                                                                                                                                                              (And.intro
                                                                                                                                                                                                                True.intro
                                                                                                                                                                                                                (And.intro
                                                                                                                                                                                                                  True.intro
                                                                                                                                                                                                                  (And.intro
                                                                                                                                                                                                                    True.intro
                                                                                                                                                                                                                    (And.intro
                                                                                                                                                                                                                      True.intro
                                                                                                                                                                                                                      (And.intro
                                                                                                                                                                                                                        True.intro
                                                                                                                                                                                                                        (And.intro
                                                                                                                                                                                                                          True.intro
                                                                                                                                                                                                                          (And.intro
                                                                                                                                                                                                                            True.intro
                                                                                                                                                                                                                            (And.intro
                                                                                                                                                                                                                              True.intro
                                                                                                                                                                                                                              (And.intro
                                                                                                                                                                                                                                True.intro
                                                                                                                                                                                                                                (And.intro
                                                                                                                                                                                                                                  True.intro
                                                                                                                                                                                                                                  (And.intro
                                                                                                                                                                                                                                    True.intro
                                                                                                                                                                                                                                    (And.intro
                                                                                                                                                                                                                                      True.intro
                                                                                                                                                                                                                                      (And.intro
                                                                                                                                                                                                                                        True.intro
                                                                                                                                                                                                                                        (And.intro
                                                                                                                                                                                                                                          True.intro
                                                                                                                                                                                                                                          (And.intro
                                                                                                                                                                                                                                            True.intro
                                                                                                                                                                                                                                            (And.intro
                                                                                                                                                                                                                                              True.intro
                                                                                                                                                                                                                                              (And.intro
                                                                                                                                                                                                                                                True.intro
                                                                                                                                                                                                                                                (And.intro
                                                                                                                                                                                                                                                  True.intro
                                                                                                                                                                                                                                                  (And.intro
                                                                                                                                                                                                                                                    True.intro
                                                                                                                                                                                                                                                    (And.intro
                                                                                                                                                                                                                                                      True.intro
                                                                                                                                                                                                                                                      (And.intro
                                                                                                                                                                                                                                                        True.intro
                                                                                                                                                                                                                                                        (And.intro
                                                                                                                                                                                                                                                          True.intro
                                                                                                                                                                                                                                                          (And.intro
                                                                                                                                                                                                                                                            True.intro
                                                                                                                                                                                                                                                            (And.intro
                                                                                                                                                                                                                                                              True.intro
                                                                                                                                                                                                                                                              (And.intro
                                                                                                                                                                                                                                                                True.intro
                                                                                                                                                                                                                                                                (And.intro
                                                                                                                                                                                                                                                                  True.intro
                                                                                                                                                                                                                                                                  (And.intro
                                                                                                                                                                                                                                                                    True.intro
                                                                                                                                                                                                                                                                    (And.intro
                                                                                                                                                                                                                                                                      True.intro
                                                                                                                                                                                                                                                                      (And.intro
                                                                                                                                                                                                                                                                        True.intro
                                                                                                                                                                                                                                                                        (And.intro
                                                                                                                                                                                                                                                                          True.intro
                                                                                                                                                                                                                                                                          (And.intro
                                                                                                                                                                                                                                                                            True.intro
                                                                                                                                                                                                                                                                            (And.intro
                                                                                                                                                                                                                                                                              True.intro
                                                                                                                                                                                                                                                                              (And.intro
                                                                                                                                                                                                                                                                                True.intro
                                                                                                                                                                                                                                                                                (And.intro
                                                                                                                                                                                                                                                                                  True.intro
                                                                                                                                                                                                                                                                                  (And.intro
                                                                                                                                                                                                                                                                                    True.intro
                                                                                                                                                                                                                                                                                    (And.intro
                                                                                                                                                                                                                                                                                      True.intro
                                                                                                                                                                                                                                                                                      (And.intro
                                                                                                                                                                                                                                                                                        True.intro
                                                                                                                                                                                                                                                                                        (And.intro
                                                                                                                                                                                                                                                                                          True.intro
                                                                                                                                                                                                                                                                                          (And.intro
                                                                                                                                                                                                                                                                                            True.intro
                                                                                                                                                                                                                                                                                            (And.intro
                                                                                                                                                                                                                                                                                              True.intro
                                                                                                                                                                                                                                                                                              (And.intro
                                                                                                                                                                                                                                                                                                True.intro
                                                                                                                                                                                                                                                                                                (And.intro
                                                                                                                                                                                                                                                                                                  True.intro
                                                                                                                                                                                                                                                                                                  (And.intro
                                                                                                                                                                                                                                                                                                    True.intro
                                                                                                                                                                                                                                                                                                    (And.intro
                                                                                                                                                                                                                                                                                                      True.intro
                                                                                                                                                                                                                                                                                                      (And.intro
                                                                                                                                                                                                                                                                                                        True.intro
                                                                                                                                                                                                                                                                                                        (And.intro
                                                                                                                                                                                                                                                                                                          True.intro
                                                                                                                                                                                                                                                                                                          (And.intro
                                                                                                                                                                                                                                                                                                            True.intro
                                                                                                                                                                                                                                                                                                            (And.intro
                                                                                                                                                                                                                                                                                                              True.intro
                                                                                                                                                                                                                                                                                                              (And.intro
                                                                                                                                                                                                                                                                                                                True.intro
                                                                                                                                                                                                                                                                                                                (And.intro
                                                                                                                                                                                                                                                                                                                  True.intro
                                                                                                                                                                                                                                                                                                                  (And.intro
                                                                                                                                                                                                                                                                                                                    True.intro
                                                                                                                                                                                                                                                                                                                    (And.intro
                                                                                                                                                                                                                                                                                                                      True.intro
                                                                                                                                                                                                                                                                                                                      (And.intro
                                                                                                                                                                                                                                                                                                                        True.intro
                                                                                                                                                                                                                                                                                                                        (And.intro
                                                                                                                                                                                                                                                                                                                          True.intro
                                                                                                                                                                                                                                                                                                                          (And.intro
                                                                                                                                                                                                                                                                                                                            True.intro
                                                                                                                                                                                                                                                                                                                            (And.intro
                                                                                                                                                                                                                                                                                                                              True.intro
                                                                                                                                                                                                                                                                                                                              (And.intro
                                                                                                                                                                                                                                                                                                                                True.intro
                                                                                                                                                                                                                                                                                                                                (And.intro
                                                                                                                                                                                                                                                                                                                                  True.intro
                                                                                                                                                                                                                                                                                                                                  (And.intro
                                                                                                                                                                                                                                                                                                                                    True.intro
                                                                                                                                                                                                                                                                                                                                    (And.intro
                                                                                                                                                                                                                                                                                                                                      True.intro
                                                                                                                                                                                                                                                                                                                                      (Eq.refl
                                                                                                                                                                                                                                                                                                                                        deepTail)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def ledger : FvdepLedger.Ledger :=
  { main := `FvdepLedgerFixtures.DeepStatement.main
    interpreter := `FvdepLedgerFixtures.DeepStatement.interpret
    plan := `FvdepLedgerFixtures.DeepStatement.plan
    libs := [`FvdepLedgerFixtures.DeepStatement]
    rows :=
      [{  component := `FvdepLedgerFixtures.DeepStatement
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims :=
            [(`FvdepLedgerFixtures.DeepStatement.statement,
                `FvdepLedgerFixtures.DeepStatement.proof)]
          subject := `FvdepLedgerFixtures.DeepStatement.plan
          path := [`FvdepLedgerFixtures.DeepStatement.main, `FvdepLedgerFixtures.DeepStatement.plan]
          noCaller := ""
          residue := []
          unproven := [] },
        { component := `FvdepLedgerFixtures.DeepStatement
          contract := "docs/contracts/U2-core.md L1–L9"
          claim := "The named statement holds for the executed subject."
          claims := []
          subject := `FvdepLedgerFixtures.DeepStatement.interpret
          path :=
            [`FvdepLedgerFixtures.DeepStatement.main, `FvdepLedgerFixtures.DeepStatement.interpret]
          noCaller := ""
          residue := []
          unproven := ["runtime"] }]
    residue :=
      [{  id := "runtime"
          what := "Fixture interpreter and optional primitive boundary."
          reason := "The effect-to-primitive mapping is tested residue."
          ruling := "Fixture interpreter mapping is trusted."
          boundary := [] }] }

end FvdepLedgerFixtures.DeepStatement
