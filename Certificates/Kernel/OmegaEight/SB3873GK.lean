
module

public import Certificates.Kernel.OmegaEight.SB3873GF

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen CFSG.KC.SBCenF

theorem MK_eqN (k m z : ℕ) :
    extMulF 65536 mulK (rowFN mulK sNfRow (wLit.getD (16 * k + m - 16) 0) (lLit.getD k 0)) z =
      MK k m z := by
  funext c d
  rw [extMulF_eq, MK, show rowFN mulK sNfRow (wLit.getD (16 * k + m - 16) 0) (lLit.getD k 0) =
    FK k m from funext (FK_eqN k m)]

theorem IK_eqN (k m z : ℕ) :
    extInv 65536 mulK invK (rowFN mulK sNfRow (wLit.getD (16 * k + m - 16) 0) (lLit.getD k 0)) z =
      IK k m z := by
  rw [IK, show rowFN mulK sNfRow (wLit.getD (16 * k + m - 16) 0) (lLit.getD k 0) =
    FK k m from funext (FK_eqN k m)]

@[expose] noncomputable def clsAtF (k m z : ℕ) (r : ℕ × ℕ) : Bool :=
  strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    decide (r.1 < 131072) && extMulF 65536 mulK (rowFN mulK sNfRow W L) z r.1 r.1 == 0 &&
      r.1 != 0 &&
      orbOKM (extMulF 65536 mulK (rowFN mulK sNfRow W L) z)
        (extInv 65536 mulK invK (rowFN mulK sNfRow W L) z) 131072 r.1
        (recM (extMulF 65536 mulK (rowFN mulK sNfRow W L) z)
          (extInv 65536 mulK invK (rowFN mulK sNfRow W L) z) t1Gens r.1) &&
      orbClosedM (extMulF 65536 mulK (rowFN mulK sNfRow W L) z)
        (extInv 65536 mulK invK (rowFN mulK sNfRow W L) z) t1Gens r.1
        (recM (extMulF 65536 mulK (rowFN mulK sNfRow W L) z)
          (extInv 65536 mulK invK (rowFN mulK sNfRow W L) z) t1Gens r.1) &&
      (recM (extMulF 65536 mulK (rowFN mulK sNfRow W L) z)
        (extInv 65536 mulK invK (rowFN mulK sNfRow W L) z) t1Gens r.1).length == r.2 &&
      (recM (extMulF 65536 mulK (rowFN mulK sNfRow W L) z)
        (extInv 65536 mulK invK (rowFN mulK sNfRow W L) z) t1Gens r.1).all
        fun p => decide (r.1 ≤ p.1)

theorem clsAtF_eq (k m z : ℕ) : clsAtF k m z = clsAt k m z := by
  funext r
  unfold clsAtF clsAt
  simp only [cen_strictB, MK_eqN, IK_eqN]

@[expose] def CenKF (k m z : ℕ) (n5 : Bool) (Q B : List ℕ) : Prop :=
  ∀ p ∈ sMarked,
    (strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
      killG (extMulF 65536 mulK (rowFN mulK sNfRow W L) z)
        (extInv 65536 mulK invK (rowFN mulK sNfRow W L) z) t1Gens 131072
        (fun r => cenLane (cenT B) (1 + Q.idxOf r)) Q
        (fun u => cenLane (cenT B) (1 + Q.length + [64, 75].idxOf u)) 8 chiF n5 p.1 p.2) = true ∧
      (strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
        queriedG (extMulF 65536 mulK (rowFN mulK sNfRow W L) z)
          (extInv 65536 mulK invK (rowFN mulK sNfRow W L) z) t1Gens
          (fun r => cenLane (cenT B) (1 + Q.idxOf r)) Q 8 chiF n5 p.1 p.2 [64, 75]) = true

theorem CenK_of_F {k m z : ℕ} {n5 : Bool} {Q B : List ℕ} (h : CenKF k m z n5 Q B) :
    CenK k m z n5 Q B := by
  intro p hp
  have := h p hp
  simp only [cen_strictB, MK_eqN, IK_eqN] at this
  exact this

end CertificateChecks.KernelO8.SB3873

end
