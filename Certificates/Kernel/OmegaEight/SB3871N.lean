module

public import Certificates.Kernel.OmegaEight.SB3871NData
public import Certificates.Kernel.OmegaEight.SB3871Blocks
public import Certificates.Kernel.OmegaEight.SB3871

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3871

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] noncomputable def MK (e v : ℕ) : ℕ := mK (e * 512 + v)

@[expose] noncomputable def cbK (j i : ℕ) : ℕ := coK (cconj mulK invK (sPc.getD j 0) (linK (2 ^ i)))

@[expose] noncomputable def olK (v : ℕ) : ℕ := if v < 512 then sKOrbRow v % 2 ^ 8 else 0

theorem M_eq : sAutData.M = MK := by
  funext e v
  simp only [sAutData, sMTab_get, MK]

theorem cb_eq : sAutData.cb = cbK := by
  funext j i
  simp only [sAutData, sConj, a9LinTab_get, a9CoTab_get, sMul_eqK, sInv_eqK, cbK]

theorem olen_eq : sAutData.olen = olK := by
  funext v
  simp only [sAutData, sKOrb_get, korbK, olK]
  split <;> simp

@[expose] def decF (w : ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | x, n + 1 => x % 2 ^ w :: decF w (x / 2 ^ w) n

@[expose] def decC : ℕ → ℕ → List (List ℕ)
  | _, 0 => []
  | x, j + 1 => decF 7 (x / 256) (x % 256) :: decC (x / 256 / 2 ^ (7 * (x % 256))) j

@[expose] def decSt (i x : ℕ) : List ℕ × List (List ℕ) := (decF 9 x i, decC (x / 2 ^ (9 * i)) 7)

@[expose] def nRaw : ℕ → List (List (List ℕ))
  | 0 => nRaw0 | 1 => nRaw1 | 2 => nRaw2 | 3 => nRaw3 | 4 => nRaw4 | 5 => nRaw5 | 6 => nRaw6
  | 7 => nRaw7 | 8 => nRaw8 | 9 => nRaw9 | _ => []

@[expose] def nLv (i : ℕ) : List (List (List (List ℕ × List (List ℕ)))) :=
  (nRaw i).map (·.map (·.map (decSt i)))

@[expose] def nBlocks (i : ℕ) : List (List (List ℕ × List (List ℕ))) := (nLv i).flatten

@[expose] def nSt (i : ℕ) : List (List ℕ × List (List ℕ)) := (nBlocks i).flatten

@[expose] noncomputable def nStepOK (i s : ℕ) : Bool :=
  ((nBlocks i).getD s []).flatMap (nStep 9 7 MK cbK olK i) == ((nLv (i + 1)).getD s []).flatten

theorem nStates_succ (i : ℕ) : nStates 9 7 MK cbK olK (i + 1) =
    (nStates 9 7 MK cbK olK i).flatMap (nStep 9 7 MK cbK olK i) := by
  simp only [nStates, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem nStates_eq (hlen : ∀ i < 9, (nLv (i + 1)).length = (nBlocks i).length)
    (hstep : ∀ i < 9, ∀ s < (nBlocks i).length, nStepOK i s = true) :
    ∀ i ≤ 9, nStates 9 7 MK cbK olK i = nSt i := by
  intro i
  induction i with
  | zero => intro _; decide +kernel
  | succ i ih =>
    intro hi
    rw [nStates_succ, ih (by omega), nSt, nBlocks, nSt, nBlocks]
    exact flatMap_blocks _ _ _ (hlen i (by omega)) fun s hs =>
      beq_iff_eq.1 (hstep i (by omega) s hs)

end CertificateChecks.KernelO8.SB3871

end
