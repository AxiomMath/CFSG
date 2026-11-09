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

theorem bindV_LLL : walkOK (vecAt TX) (otL (otL (otL (hnsOrbitData ()).vectors)))
    (nat_lit 0) = true := by
  quickRfl
theorem bindV_LLR : walkOK (vecAt TX) (otR (otL (otL (hnsOrbitData ()).vectors)))
    (Nat.add (nat_lit 0) (otS (otL (otL (hnsOrbitData ()).vectors)))) = true := by
  quickRfl
theorem bindV_LRL : walkOK (vecAt TX) (otL (otR (otL (hnsOrbitData ()).vectors)))
    (Nat.add (nat_lit 0) (otS (otL (hnsOrbitData ()).vectors))) = true := by
  quickRfl
theorem bindV_LRR : walkOK (vecAt TX) (otR (otR (otL (hnsOrbitData ()).vectors)))
    (Nat.add (Nat.add (nat_lit 0) (otS (otL (hnsOrbitData ()).vectors))) (otS (otR (otL (hnsOrbitData ()).vectors)))) = true := by
  quickRfl
theorem bindV_RLL : walkOK (vecAt TX) (otL (otL (otR (hnsOrbitData ()).vectors)))
    (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).vectors)) = true := by
  quickRfl
theorem bindV_RLR : walkOK (vecAt TX) (otR (otL (otR (hnsOrbitData ()).vectors)))
    (Nat.add (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).vectors)) (otS (otL (otR (hnsOrbitData ()).vectors)))) = true := by
  quickRfl
theorem bindV_RRL : walkOK (vecAt TX) (otL (otR (otR (hnsOrbitData ()).vectors)))
    (Nat.add (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).vectors)) (otS (otR (hnsOrbitData ()).vectors))) = true := by
  quickRfl
theorem bindV_RRR : walkOK (vecAt TX) (otR (otR (otR (hnsOrbitData ()).vectors)))
    (Nat.add (Nat.add (Nat.add (nat_lit 0) (otS (hnsOrbitData ()).vectors)) (otS (otR (hnsOrbitData ()).vectors))) (otS (otR (otR (hnsOrbitData ()).vectors)))) = true := by
  quickRfl

theorem bindV : walkOK (vecAt TX) (hnsOrbitData ()).vectors (nat_lit 0) = true :=
  (walkOK_of_br (by quickRfl)
    (walkOK_of_br (by quickRfl)
    (walkOK_of_br (by quickRfl)
    bindV_LLL
    bindV_LLR)
    (walkOK_of_br (by quickRfl)
    bindV_LRL
    bindV_LRR))
    (walkOK_of_br (by quickRfl)
    (walkOK_of_br (by quickRfl)
    bindV_RLL
    bindV_RLR)
    (walkOK_of_br (by quickRfl)
    bindV_RRL
    bindV_RRR)))

theorem neg_vecAt : Bool.not (vecAt TX (nat_lit 1) (fldW (getRec TX (nat_lit 464) (nat_lit 0))
    (nat_lit 0) (nat_lit 399))) = true := by quickRfl
theorem neg_walk : Bool.not (walkOK (vecAt TX) (.leaf (nat_lit 399) (nat_lit 1)
    (fldW (getRec TX (nat_lit 464) (nat_lit 1)) (nat_lit 0) (nat_lit 399))) (nat_lit 0)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.HNXBind

end
