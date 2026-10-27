module

public import Certificates.Kernel.FiveStd.Data
public import Certificates.Data.Kernel.FiveStdKList
public import Certificates.Data.Kernel.FiveStdKDiag
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

set_option Elab.async false

@[expose] def X1c : List Nat := [29501, 19753, 21502, 30504, 82001, 94501]

@[expose] def Y1c : List Nat := [78797, 78812, 78842, 78857, 78881, 78901]

@[expose] def XP : List Nat :=
  [1130445697853, 2229957429132, 3329469032281, 4428980670808, 1120224169257, 2219735875909,
    3319247522808, 4418759186335, 1122058130430, 2221569891583, 3321081500982, 4420593089509,
    1131497420584, 2231009138360, 3330520791509, 4430032405036, 1185495990353, 2285007621254,
    3384519252155, 4484030883056, 1198603202853, 2298114846254, 3397626489655, 4497138133056]

@[expose] def YP : List Nat :=
  [1182136349645, 2281647977942, 3381159605614, 4480671233281, 1182152078300, 2281663706637,
    3381175334199, 4480686961906, 1182183535610, 2281695163827, 3381206791569, 4480718419156,
    1182199264265, 2281710892522, 3381222520154, 4480734147781, 1182224430113, 2281736057894,
    3381247685675, 4480759313456, 1182245401653, 2281757029454, 3381268657255, 4480780285056]

@[expose] def eC (e : Nat) : Nat := e % 1048576

@[expose] def eG (e : Nat) : Nat := e / 1048576 % 1048576

@[expose] def eJ (e : Nat) : Nat := e / 1099511627776

@[expose] noncomputable def tabOK (P C : List Nat) : Bool :=
  P.all fun e => C.contains (eG e) && decide (eJ e < 5) && Nat.beq (powK (eG e) (eJ e)) (eC e)

theorem tab_x : tabOK XP X1c = true := by decide +kernel

theorem tab_y : tabOK YP Y1c = true := by decide +kernel

@[expose] noncomputable def memP (P : List Nat) (c : Nat) : Bool := P.any fun e => Nat.beq (eC e) c

@[expose] noncomputable def sylRec (c : Nat) : Bool :=
  letB (invK c) fun ci => letB (cjK c ci 29501) fun cx => letB (cjK c ci 78797) fun cy =>
    orB (andB (memP XP cx) (memP YP cy)) (andB (memP YP cx) (memP XP cy))

noncomputable abbrev spt : Nat → Bool := fun i => sylRec (rCode (f64 T i))

@[expose] noncomputable def sF (k : Nat) : Bool := allR (900 * k) 900 spt

#kc_each_unfold sF 0 32 as CertificateChecks.FiveStd.ch5147s

#kc_forall_chunks sylcK (fun k => allR (900 * k) 900 spt = true) 32
  CertificateChecks.FiveStd.ch5147s 1

theorem sylc_chunks : ∀ k < 32, allR (900 * k) 900 spt = true := sylcK

theorem tab_x_neg : (!tabOK (XP.set 0 (XP.getD 0 0 + 1099511627776)) X1c) = true := by decide +kernel

theorem sylc_neg : (!allR 0 900 fun i => letB (invK (rCode (f64 T i))) fun ci =>
    letB (cjK (rCode (f64 T i)) ci 29501) fun cx => letB (cjK (rCode (f64 T i)) ci 78797) fun cy =>
      orB (andB (memP XP cx) (memP (YP.take 20) cy)) (andB (memP (YP.take 20) cx) (memP XP cy))) = true := by
  decide +kernel

end CertificateChecks.FiveStd

end
