module

public import Certificates.Data.Kernel.PCentSet
public import Certificates.Kernel.HS799102.GlueData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

#kc_repo #kc_json_gz CertificateChecks.KernelHS799102
  "Certificates/Kernel/HS799102/data/inv.json.gz" 333115 18440860589895312762
  (RG : List Nat) (P0 : List (Nat × Nat × Nat × Nat)) (HW : List (List Nat)) (HG : List Nat)
  (SM : Nat) (SR : List (Nat × Nat × Nat × Nat)) (NW : List (List Nat)) (NG : List Nat)
  (NL : List (Nat × Nat × Nat × Nat))

open CFSG.KC.Enum (pg pcomp pidn allN)
open CFSG.KS (mask pinvS)
open CFSG.KC.PCent (wordK allL imgM)

@[expose] noncomputable def rG (k : Nat) : Nat := RG.getD k (nat_lit 0)

@[expose] noncomputable def hG (k : Nat) : Nat := HG.getD k (nat_lit 0)

@[expose] noncomputable def nG (k : Nat) : Nat := NG.getD k (nat_lit 0)

@[expose] noncomputable def mulI (x y : Nat) : Nat := pcomp 100 7 (mask 7) x y

@[expose] noncomputable def commI (x y : Nat) : Bool := Nat.beq (mulI x y) (mulI y x)

@[expose] noncomputable def rGBind : Bool :=
  Nat.beq (rG 0) (CertificateChecks.KernelHS100.HP.F 0) &&
    Nat.beq (rG 1) (CertificateChecks.KernelHS100.HP.F 1) &&
    Nat.beq (rG 2) (CertificateChecks.KernelHS100.HP.F 15) &&
    Nat.beq (rG 3) (pinvS 100 7 (mask 7) (CertificateChecks.KernelHS100.HP.F 0)) &&
    Nat.beq (rG 4) (pinvS 100 7 (mask 7) (CertificateChecks.KernelHS100.HP.F 1)) &&
    Nat.beq (rG 5) (pinvS 100 7 (mask 7) (CertificateChecks.KernelHS100.HP.F 15))

@[expose] noncomputable def wordsK (G : Nat → Nat) (W : List (List Nat)) (m : Nat) : Bool :=
  allN m (fun k => Nat.beq (G k) (wordK 100 7 rG (W.getD k [])) &&
    allL (fun c => Nat.blt c (nat_lit 6)) (W.getD k []))

@[expose] noncomputable def ivK : Bool :=
  allN 3 (fun j => Nat.beq (mulI (TH.F (Nat.add 2 j)) (TH.F (Nat.add 2 j))) (pidn 100 7) &&
    commI (TH.F (Nat.add 2 j)) (TH.F 0) && commI (TH.F (Nat.add 2 j)) (TH.F 1)) &&
    siftB (mulI (TH.F 2) (rG 5)) && siftB (mulI (TH.F 3) (rG 5)) && siftB (TH.F 4)

@[expose] noncomputable def fixK : Bool :=
  Nat.beq (pg 7 (mask 7) (TH.F 0) 0) 0 && Nat.beq (pg 7 (mask 7) (TH.F 1) 0) 0 &&
    allN 100 (fun y => !(Nat.beq (pg 7 (mask 7) (TH.F 0) y) y &&
      Nat.beq (pg 7 (mask 7) (TH.F 1) y) y) || Nat.beq y 0 ||
      Nat.beq y (pg 7 (mask 7) (TH.F 2) 0) || Nat.beq y (pg 7 (mask 7) (TH.F 3) 0) ||
      Nat.beq y (pg 7 (mask 7) (TH.F 4) 0))

@[expose] noncomputable def smK : Bool :=
  allN 100 (fun i => Bool.beq (Nat.testBit SM i) (Nat.beq (pg 7 (mask 7) (TH.F 0) i) i))

@[expose] noncomputable def isV (y : Nat) : Bool :=
  Nat.beq y (pidn 100 7) || Nat.beq y (TH.F 2) || Nat.beq y (TH.F 3) || Nat.beq y (TH.F 4)

@[expose] noncomputable def invT (y : Nat) : Bool :=
  !Nat.beq (mulI y y) (pidn 100 7) || isV y

@[expose] noncomputable def tV (j : Nat) : Nat := [pidn 100 7, TH.F 2, TH.F 3, TH.F 4].getD j 0

@[expose] noncomputable def scanK : Bool :=
  allL (fun x => !(commI x (TH.F 0) && commI x (TH.F 1)) ||
    allN 4 (fun j => invT (mulI (tV j) x))) (NL.map Prod.fst)

end CertificateChecks.KernelHS799102

end
