module

public import Certificates.Kernel.TwistDce3.ON.Data
public import Certificates.Kernel.TwistDce3.ON.CoverData
public import Certificates.Data.Kernel.TwistDce2.Rels
public import CFSG.Sporadic.Recognition.ONMultiplierInputs

public section

namespace CFSG.KD.ONDce3

open CFSG.KC.TwDce2 CFSG.CosetTable CFSG.Sporadic.Recognition.ONMultiplier
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.LieType.Multipliers

@[expose] def onSw (c : ℕ) : ℕ :=
  if c = 2 then 4 else if c = 3 then 5 else if c = 4 then 2 else if c = 5 then 3 else c

@[expose] noncomputable def FS (c : ℕ) : ℕ := FB (onSw c)

@[expose] def INVQ : ℕ := ((List.range 16).map fun c => (if c < 12 then c ^^^ 1 else c) * 16 ^ c).sum

@[expose] def onQCodes : List (List ℕ) :=
  (restrictWords (subsetOf 4 [0, 1, 2]) (coverWords onRels onCommWord ++ squareWords onRels)).map
    (·.map fun l => bif l.2 then 2 * l.1.val else 2 * l.1.val + 1)

theorem f_id_ok : ∀ c < 12, 6 ≤ c → ∀ p < 57, CFSG.KC.YModel.fieldAt PB (F c) p = p := by
  decide +kernel

theorem q_letters_ok : lettersOK FS INVQ 57 = true := by
  decide +kernel

theorem q_inv_ok : invCodesOK INVQ 6 = true := by
  decide +kernel

theorem q_codes_len : ∀ w ∈ onQCodes, w.length < 2 ^ 32 := by
  decide +kernel

theorem q_rels_ok : relsOK FS 57 onQCodes = true := by
  decide +kernel

end CFSG.KD.ONDce3

end
