module

public import Certificates.Kernel.SporSch.HN.GenF5T
public import Certificates.Kernel.SporSch.HN.Seeds2106K
public import Certificates.Data.Kernel.SporSch.HNF5KronT
public import CFSG.Sporadic.HNSchreier.SepCheckInputs
meta import CFSG.Sporadic.HNSchreier.SepCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.HNForm CFSG.Sporadic.HNSchreier.Data.formPayload

namespace CertificateChecks.KernelHNChain.Form

open CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native

meta def mats : List (Array (Array Nat)) :=
  let m := mulM 5 133
  let M := rowsM
  let At := colsMat 133 rowsA
  let Bt := colsMat 133 rowsB
  let Mi := invM 5 133 M
  [rowsA, rowsB, M, colsMat 133 M, Mi, m M Mi, At, m At M, m (m At M) rowsA, Bt, m Bt M,
    m (m Bt M) rowsB]

meta def spec : List (Nat × Nat × Nat) :=
  [(2, 0, 0), (2, 0, 0), (2, 0, 0), (3, 2, 0), (2, 0, 0), (0, 2, 4), (3, 0, 0), (0, 6, 2),
    (0, 7, 0), (3, 1, 0), (0, 9, 2), (0, 10, 1)]

end CertificateChecks.KernelHNChain.Form

#kss_f5tree CertificateChecks.KernelHNChain.HNF CertificateChecks.KernelHNChain.Form.mats
  CertificateChecks.KernelHNChain.Form.spec

namespace CertificateChecks.KernelHNChain.Form

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelHNChain

@[expose] noncomputable def sf (k i : Nat) : Nat := slice5 HNF.MT k i

theorem eqA : allN 133 (fun i => Nat.beq (sf 0 i) (HNSeeds.sl 0 i)) = true := by quickRfl
theorem eqB : allN 133 (fun i => Nat.beq (sf 1 i) (HNSeeds.sl 1 i)) = true := by quickRfl
theorem payM : pay5K (sf 2) HNForm.chars = true := by quickRfl

theorem blk0 : krBlkT HNF.MT HNF.OP HNF.L HNF.R 0 12 = true := by quickRfl

theorem specLt : allN 12 (fun k => bAnd(Nat.blt (HNF.L k) 12, Nat.blt (HNF.R k) 12)) = true := by
  quickRfl

theorem sym : allN 133 (fun i => Nat.beq (sf 3 i) (sf 2 i)) = true := by quickRfl
theorem id5 : allN 133 (fun i => Nat.beq (sf 5 i) (idRow5 i)) = true := by quickRfl
theorem invA : allN 133 (fun i => Nat.beq (sf 8 i) (sf 2 i)) = true := by quickRfl
theorem invB : allN 133 (fun i => Nat.beq (sf 11 i) (sf 2 i)) = true := by quickRfl

theorem neg_sym : Bool.not (allN 133 (fun i => Nat.beq (sf 6 i) (sf 0 i))) = true := by quickRfl
theorem neg_inv : Bool.not (allN 133 (fun i => Nat.beq (sf 7 i) (sf 2 i))) = true := by quickRfl
theorem neg_pay : Bool.not (pay5K (sf 3 ∘ Nat.succ) HNForm.chars) = true := by quickRfl

end CertificateChecks.KernelHNChain.Form

end
