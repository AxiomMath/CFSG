module

public import CFSG.Certificates.Kernel.E27Orth.GlueThree
public import Certificates.Kernel.E27Orth.O73Base
public import Certificates.Kernel.E27Orth.O73Conj

public section

namespace CertificateChecks.KernelE27Orth.O73

open CFSG.KS.Ord CFSG.KD.E27Orth Subgroup Matrix CFSG.RankThree.PartOne.N143.O7

theorem o73131009_gram :
    ∀ j : Fin 3, (ordMat 3 7 6 42 (G j))ᵀ * gr7 * ordMat 3 7 6 42 (G j) = gr7 := by
  decide +kernel

theorem o73131009_gramY :
    ∀ j : Fin 3, (ordMat 3 7 6 42 (Y j))ᵀ * gr7 * ordMat 3 7 6 42 (Y j) = gr7 := by
  decide +kernel

theorem o73131009_inv : ∀ j : Fin 3, ordMat 3 7 6 42 (Y j) * ordMat 3 7 6 42 (G j) =
    ordMat 3 7 6 42 (G j) * ordMat 3 7 6 42 (G j) * ordMat 3 7 6 42 (Y j) := by
  decide +kernel

theorem o73131009_lu : ∀ j : Fin 3,
    Matrix.of (fun a b : Fin 7 => if a ≤ b then ordMat 3 7 6 42 (G j) a b else 0) = 1 := by
  decide +kernel

theorem o73131009_fact : ∃ S : Subgroup ↥Om, Nat.card S = 3 ^ 9 ∧
    ∀ s ∈ S, orderOf s = 3 → 81 ∣ Nat.card ↥(S ⊓ centralizer ({s} : Set ↥Om)) :=
  syl_glue o73131009_consts o73131009_gram o73131009_gramY o73131009_inv o73131009_lu
    o73131009_base (all_of_blocks (f := CFSG.KC.E27Orth.treeI mulO cnO ONE 3 G E Tr) o73131009_tree)
    (all_of_blocks (f := CFSG.KC.E27Orth.keyI 19683 E Ss) o73131009_key)
    (all_of_blocks (f := CFSG.KC.E27Orth.conjI mulO 19683 164 E Rp W) o73131009_conj)
    (all_of_blocks (f := CFSG.KC.E27Orth.repI mulO cnO ONE 19683 81 E Rp Cm) o73131009_rep)

end CertificateChecks.KernelE27Orth.O73

end
