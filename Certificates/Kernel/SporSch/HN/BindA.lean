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

theorem bindA_LLL : walkOK (imgAt TX (nat_lit 0)) (otL (otL (otL (hnsOrbitData ()).alpha)))
    (nat_lit 0) = true := by
  quickRfl
theorem bindA_LLR : walkOK (imgAt TX (nat_lit 0)) (otR (otL (otL (hnsOrbitData ()).alpha)))
    (Nat.add (nat_lit 0) (otS (otL (otL (hnsOrbitData ()).alpha)))) = true := by
  quickRfl
theorem bindA_LRL : walkOK (imgAt TX (nat_lit 0)) (otL (otR (otL (hnsOrbitData ()).alpha)))
    (Nat.add (nat_lit 0) (otS (otL (hnsOrbitData ()).alpha))) = true := by
  quickRfl
theorem bindA_LRR : walkOK (imgAt TX (nat_lit 0)) (otR (otR (otL (hnsOrbitData ()).alpha)))
    (Nat.add (Nat.add (nat_lit 0) (otS (otL (hnsOrbitData ()).alpha))) (otS (otR (otL (hnsOrbitData ()).alpha)))) = true := by
  quickRfl
theorem bindA_RLL : walkOK (imgAt TX (nat_lit 0)) (otL (otL (otR (hnsOrbitData ()).alpha)))
    (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).alpha)) = true := by
  quickRfl
theorem bindA_RLR : walkOK (imgAt TX (nat_lit 0)) (otR (otL (otR (hnsOrbitData ()).alpha)))
    (Nat.add (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).alpha)) (otS (otL (otR (hnsOrbitData ()).alpha)))) = true := by
  quickRfl
theorem bindA_RRL : walkOK (imgAt TX (nat_lit 0)) (otL (otR (otR (hnsOrbitData ()).alpha)))
    (Nat.add (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).alpha)) (otS (otR (hnsOrbitData ()).alpha))) = true := by
  quickRfl
theorem bindA_RRR : walkOK (imgAt TX (nat_lit 0)) (otR (otR (otR (hnsOrbitData ()).alpha)))
    (Nat.add (Nat.add (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).alpha)) (otS (otR (hnsOrbitData ()).alpha))) (otS (otR (otR (hnsOrbitData ()).alpha)))) = true := by
  quickRfl

theorem bindA : walkOK (imgAt TX (nat_lit 0)) (hnsOrbitData ()).alpha (nat_lit 0) = true :=
  (walkOK_of_br (by quickRfl)
    (walkOK_of_br (by quickRfl)
    (walkOK_of_br (by quickRfl)
    bindA_LLL
    bindA_LLR)
    (walkOK_of_br (by quickRfl)
    bindA_LRL
    bindA_LRR))
    (walkOK_of_br (by quickRfl)
    (walkOK_of_br (by quickRfl)
    bindA_RLL
    bindA_RLR)
    (walkOK_of_br (by quickRfl)
    bindA_RRL
    bindA_RRR)))
theorem bindB_LLL : walkOK (imgAt TX (nat_lit 1)) (otL (otL (otL (hnsOrbitData ()).beta)))
    (nat_lit 0) = true := by
  quickRfl
theorem bindB_LLR : walkOK (imgAt TX (nat_lit 1)) (otR (otL (otL (hnsOrbitData ()).beta)))
    (Nat.add (nat_lit 0) (otS (otL (otL (hnsOrbitData ()).beta)))) = true := by
  quickRfl
theorem bindB_LRL : walkOK (imgAt TX (nat_lit 1)) (otL (otR (otL (hnsOrbitData ()).beta)))
    (Nat.add (nat_lit 0) (otS (otL (hnsOrbitData ()).beta))) = true := by
  quickRfl
theorem bindB_LRR : walkOK (imgAt TX (nat_lit 1)) (otR (otR (otL (hnsOrbitData ()).beta)))
    (Nat.add (Nat.add (nat_lit 0) (otS (otL (hnsOrbitData ()).beta))) (otS (otR (otL (hnsOrbitData ()).beta)))) = true := by
  quickRfl
theorem bindB_RLL : walkOK (imgAt TX (nat_lit 1)) (otL (otL (otR (hnsOrbitData ()).beta)))
    (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).beta)) = true := by
  quickRfl
theorem bindB_RLR : walkOK (imgAt TX (nat_lit 1)) (otR (otL (otR (hnsOrbitData ()).beta)))
    (Nat.add (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).beta)) (otS (otL (otR (hnsOrbitData ()).beta)))) = true := by
  quickRfl
theorem bindB_RRL : walkOK (imgAt TX (nat_lit 1)) (otL (otR (otR (hnsOrbitData ()).beta)))
    (Nat.add (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).beta)) (otS (otR (hnsOrbitData ()).beta))) = true := by
  quickRfl
theorem bindB_RRR : walkOK (imgAt TX (nat_lit 1)) (otR (otR (otR (hnsOrbitData ()).beta)))
    (Nat.add (Nat.add (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).beta)) (otS (otR (hnsOrbitData ()).beta))) (otS (otR (otR (hnsOrbitData ()).beta)))) = true := by
  quickRfl

theorem bindB : walkOK (imgAt TX (nat_lit 1)) (hnsOrbitData ()).beta (nat_lit 0) = true :=
  (walkOK_of_br (by quickRfl)
    (walkOK_of_br (by quickRfl)
    (walkOK_of_br (by quickRfl)
    bindB_LLL
    bindB_LLR)
    (walkOK_of_br (by quickRfl)
    bindB_LRL
    bindB_LRR))
    (walkOK_of_br (by quickRfl)
    (walkOK_of_br (by quickRfl)
    bindB_RLL
    bindB_RLR)
    (walkOK_of_br (by quickRfl)
    bindB_RRL
    bindB_RRR)))

theorem neg_imgAt : Bool.not (imgAt TX (nat_lit 0) (nat_lit 0)
    (fldW (getRec TX (nat_lit 464) (nat_lit 0)) (nat_lit 420) (nat_lit 21))) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNXBind

end
