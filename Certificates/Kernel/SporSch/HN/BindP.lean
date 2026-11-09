module

public import Certificates.Data.Kernel.SporSch.HNXBind
public import Certificates.Kernel.SporSch.HN.BindSplit
public import CFSG.Certificates.Kernel.Local.HN.X.Data
public import CFSG.Sporadic.HNSchreier.EmbeddedOrbit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSporSch.HNXBind

open CFSG.KC.Enum CFSG.KC.LL CFSG.KS.SporSch CFSG.KD.LgHNX CFSG.Sporadic.HNSchreier.Native

theorem bindP_LLL : walkOK (parAt TX) (otL (otL (otL (hnsOrbitData ()).parents)))
    (nat_lit 0) = true := by
  quickRfl
theorem bindP_LLR : walkOK (parAt TX) (otR (otL (otL (hnsOrbitData ()).parents)))
    (Nat.add (nat_lit 0) (otS (otL (otL (hnsOrbitData ()).parents)))) = true := by
  quickRfl
theorem bindP_LRL : walkOK (parAt TX) (otL (otR (otL (hnsOrbitData ()).parents)))
    (Nat.add (nat_lit 0) (otS (otL (hnsOrbitData ()).parents))) = true := by
  quickRfl
theorem bindP_LRR : walkOK (parAt TX) (otR (otR (otL (hnsOrbitData ()).parents)))
    (Nat.add (Nat.add (nat_lit 0) (otS (otL (hnsOrbitData ()).parents))) (otS (otR (otL (hnsOrbitData ()).parents)))) = true := by
  quickRfl
theorem bindP_RLL : walkOK (parAt TX) (otL (otL (otR (hnsOrbitData ()).parents)))
    (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).parents)) = true := by
  quickRfl
theorem bindP_RLR : walkOK (parAt TX) (otR (otL (otR (hnsOrbitData ()).parents)))
    (Nat.add (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).parents)) (otS (otL (otR (hnsOrbitData ()).parents)))) = true := by
  quickRfl
theorem bindP_RRL : walkOK (parAt TX) (otL (otR (otR (hnsOrbitData ()).parents)))
    (Nat.add (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).parents)) (otS (otR (hnsOrbitData ()).parents))) = true := by
  quickRfl
theorem bindP_RRR : walkOK (parAt TX) (otR (otR (otR (hnsOrbitData ()).parents)))
    (Nat.add (Nat.add (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).parents)) (otS (otR (hnsOrbitData ()).parents))) (otS (otR (otR (hnsOrbitData ()).parents)))) = true := by
  quickRfl

theorem bindP : walkOK (parAt TX) (hnsOrbitData ()).parents (nat_lit 0) = true :=
  (walkOK_of_br (by quickRfl)
    (walkOK_of_br (by quickRfl)
    (walkOK_of_br (by quickRfl)
    bindP_LLL
    bindP_LLR)
    (walkOK_of_br (by quickRfl)
    bindP_LRL
    bindP_LRR))
    (walkOK_of_br (by quickRfl)
    (walkOK_of_br (by quickRfl)
    bindP_RLL
    bindP_RLR)
    (walkOK_of_br (by quickRfl)
    bindP_RRL
    bindP_RRR)))
theorem bindL_LLL : walkOK (labAt TX) (otL (otL (otL (hnsOrbitData ()).labels)))
    (nat_lit 0) = true := by
  quickRfl
theorem bindL_LLR : walkOK (labAt TX) (otR (otL (otL (hnsOrbitData ()).labels)))
    (Nat.add (nat_lit 0) (otS (otL (otL (hnsOrbitData ()).labels)))) = true := by
  quickRfl
theorem bindL_LRL : walkOK (labAt TX) (otL (otR (otL (hnsOrbitData ()).labels)))
    (Nat.add (nat_lit 0) (otS (otL (hnsOrbitData ()).labels))) = true := by
  quickRfl
theorem bindL_LRR : walkOK (labAt TX) (otR (otR (otL (hnsOrbitData ()).labels)))
    (Nat.add (Nat.add (nat_lit 0) (otS (otL (hnsOrbitData ()).labels))) (otS (otR (otL (hnsOrbitData ()).labels)))) = true := by
  quickRfl
theorem bindL_RLL : walkOK (labAt TX) (otL (otL (otR (hnsOrbitData ()).labels)))
    (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).labels)) = true := by
  quickRfl
theorem bindL_RLR : walkOK (labAt TX) (otR (otL (otR (hnsOrbitData ()).labels)))
    (Nat.add (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).labels)) (otS (otL (otR (hnsOrbitData ()).labels)))) = true := by
  quickRfl
theorem bindL_RRL : walkOK (labAt TX) (otL (otR (otR (hnsOrbitData ()).labels)))
    (Nat.add (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).labels)) (otS (otR (hnsOrbitData ()).labels))) = true := by
  quickRfl
theorem bindL_RRR : walkOK (labAt TX) (otR (otR (otR (hnsOrbitData ()).labels)))
    (Nat.add (Nat.add (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).labels)) (otS (otR (hnsOrbitData ()).labels))) (otS (otR (otR (hnsOrbitData ()).labels)))) = true := by
  quickRfl

theorem bindL : walkOK (labAt TX) (hnsOrbitData ()).labels (nat_lit 0) = true :=
  (walkOK_of_br (by quickRfl)
    (walkOK_of_br (by quickRfl)
    (walkOK_of_br (by quickRfl)
    bindL_LLL
    bindL_LLR)
    (walkOK_of_br (by quickRfl)
    bindL_LRL
    bindL_LRR))
    (walkOK_of_br (by quickRfl)
    (walkOK_of_br (by quickRfl)
    bindL_RLL
    bindL_RLR)
    (walkOK_of_br (by quickRfl)
    bindL_RRL
    bindL_RRR)))

theorem neg_parAt : Bool.not (parAt TX (nat_lit 1) (nat_lit 1)) = true := by quickRfl
theorem neg_labAt : Bool.not (labAt TX (nat_lit 1) (nat_lit 1)) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNXBind

end
