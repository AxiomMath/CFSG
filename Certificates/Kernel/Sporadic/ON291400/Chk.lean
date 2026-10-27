module

public import Certificates.Kernel.Sporadic.OddCore.ON2129
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.Schreier.ONCheckSmallAuxInputs
meta import CFSG.Sporadic.Schreier.ONCheckSmallAuxInputs
meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON291400

open CFSG.ONSchreier CFSG.PSL3Four.Native

meta def iSelM : List Nat :=
  (List.range t32Enum.tabs.size).filter fun i =>
    comp 32 t32Enum.tabs[i]! t32Enum.tabs[i]! == idTab 32 && !(t32Enum.tabs[i]! == idTab 32)

meta def iPM : Array (Array Nat) :=
  (iSelM.map fun i => #[CFSG.KS.RawGen.pack 6 t32Enum.tabs[i]!]).toArray

meta def cmM : Array (Array Nat) :=
  let I := iSelM.map fun i => t32Enum.tabs[i]!
  (I.map fun a => (I.map fun b => if comp 32 a b == comp 32 b a then 1 else 0).toArray).toArray

end CertificateChecks.KernelSpor.ON291400

#knatlist CertificateChecks.KernelSpor.ON291400.ISel CertificateChecks.KernelSpor.ON291400.iSelM
#kmisc_packarrs CertificateChecks.KernelSpor.ON291400.IPT CertificateChecks.KernelSpor.ON291400.iPM
  192
#kmisc_packarrs CertificateChecks.KernelSpor.ON291400.CMR CertificateChecks.KernelSpor.ON291400.cmM
  1

namespace CertificateChecks.KernelSpor.ON291400

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KLie.CT (fget andB orB notB)

@[expose] noncomputable def pc (x y : Nat) : Nat := pcomp 32 6 (mask 6) x y

@[expose] noncomputable def qI (i : Nat) : Bool :=
  strictB (T32E.T i) fun t =>
    andB (Nat.beq (pc t t) (pidn 32 6)) (notB (Nat.beq t (pidn 32 6)))

@[expose] noncomputable def cmB (i l : Nat) : Bool := Nat.beq (fget (CMR i) l 1) 1

@[expose] noncomputable def fourthK (i j k : Nat) : Bool :=
  strictB (IPT i) fun a => strictB (IPT j) fun b => strictB (IPT k) fun c =>
  strictB (pc a b) fun ab => strictB (pc a c) fun ac => strictB (pc b c) fun bc =>
  strictB (pc ab c) fun abc =>
    allN 87 fun l => strictB (IPT l) fun x =>
      orB (notB (andB (andB (cmB i l) (cmB j l)) (cmB k l)))
        (orB (Nat.beq x a) (orB (Nat.beq x b) (orB (Nat.beq x c) (orB (Nat.beq x ab)
          (orB (Nat.beq x ac) (orB (Nat.beq x bc) (Nat.beq x abc)))))))

@[expose] noncomputable def thirdK (i j : Nat) : Bool :=
  strictB (pc (IPT i) (IPT j)) fun ab =>
    allN 87 fun k =>
      orB (notB (andB (cmB i k) (cmB j k))) (orB (Nat.beq k i) (orB (Nat.beq k j)
        (orB (Nat.beq (IPT k) ab) (fourthK i j k))))

@[expose] noncomputable def noE16K : Bool :=
  allN 87 fun i => allN 87 fun j => orB (notB (cmB i j)) (orB (Nat.beq i j) (thirdK i j))

theorem k_sel : bAnd(selFrom qI 512 0 ISel, Nat.beq ISel.length 87) = true := by
  quickRfl

theorem k_bind : allN 87 (fun i => Nat.beq (IPT i) (T32E.T (ISel.getD i 0))) = true := by
  quickRfl

@[expose] noncomputable def bEqK (x y : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB y) y x

theorem k_cm : allN 87 (fun i => allN 87 (fun l =>
    bEqK (cmB i l) (Nat.beq (pc (IPT i) (IPT l)) (pc (IPT l) (IPT i))))) = true := by
  quickRfl

theorem k_main : noE16K = true := by
  quickRfl

end CertificateChecks.KernelSpor.ON291400

end
