-- No universal final judge (Paper 40): institutional interpretation of Paper 30 barrier
-- When composed with Learning in nems-lean, the barrier hypothesis is supplied by that library.

variable (Instance : Type*) (Claim : Instance → Prop)

/-- Statement of the diagonal barrier: no total, sound, complete internal certifier exists
    for nontrivial extensional claim predicates. (Proved in Learning/Paper 30.) -/
def DiagBarrier : Prop :=
  ∀ (Certifier : Instance → Bool), ¬((∀ i, Certifier i = true ↔ Claim i) ∧ (∀ i, Certifier i = false ↔ ¬ Claim i))

/-- An institution is a universal final judge for Claim if it provides such a certifier. -/
def UniversalJudge (Certifier : Instance → Bool) : Prop :=
  (∀ i, Certifier i = true ↔ Claim i) ∧ (∀ i, Certifier i = false ↔ ¬ Claim i)

/-- Under the diagonal barrier, no institution can be a universal final judge. -/
theorem no_universal_final_judge (h : DiagBarrier) (c : Instance → Bool) :
    ¬ UniversalJudge c := fun ⟨h1, h2⟩ => h c ⟨h1, h2⟩
