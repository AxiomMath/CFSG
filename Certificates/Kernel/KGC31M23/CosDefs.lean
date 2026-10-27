module

public import Certificates.Kernel.KGC31M23.Defs
public import Certificates.Kernel.KGC31M23.ConjData
public import Certificates.Data.Kernel.KGC31PB

public section

namespace CertificateChecks.KernelKGC31M23

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KS.SporSch.MOC
open CFSG.Quasithin.KGC31.M23 CertificateChecks.KernelSporSch

@[expose] def wI (l : List Nat) : List Int := l.map Int.ofNat

@[expose] noncomputable def B0 : Nat := pw (wW.headD [])

@[expose] noncomputable def Z : Nat := pw (wI CFSG.KD.M23Conj.z)

@[expose] noncomputable def CB : List Nat :=
  (pfilterProducts 23 5 (fun _ => true) (trPL 23 5 M23C1.LR M23C1.TR 4) (pidn 23 5) []).map
    (pcj 23 5 Z (pinv 23 5 Z))

@[expose] noncomputable def pfix (pts : List Nat) (X : Nat) : Bool :=
  pts.all fun i => Nat.beq (pg 5 (mask 5) X i) i

@[expose] noncomputable def pfixSet (bs pts : List Nat) : Bool :=
  (List.range 23).all fun i => (bs.all fun b => Nat.beq (pg 5 (mask 5) b i) i) == pts.contains i

@[expose] noncomputable def conjOK (bs : List Nat) (N R : Nat) : Bool :=
  Nat.beq (pcj 23 5 N (pinv 23 5 N) B0) (pcj 23 5 R (pinv 23 5 R) B0) &&
    pnormAll 23 5 bs N (pinv 23 5 N)

@[expose] noncomputable def rW (m : Nat) : Nat := pw (wCosetW.getD m [])
@[expose] noncomputable def rT (m : Nat) : Nat := pw (tCosetW.getD m [])
@[expose] noncomputable def rE (m : Nat) : Nat := pw (eCosetW.getD m [])

@[expose] noncomputable def nTP (m : Nat) : Nat := pw (wI (CFSG.KD.M23Conj.nT.getD m []))
@[expose] noncomputable def nEP (m : Nat) : Nat := pw (wI (CFSG.KD.M23Conj.nE.getD m []))

@[expose] noncomputable def fT (c : Nat) : Bool := pnormAll 23 5 tP c (pinv 23 5 c) && pfix triT c

end CertificateChecks.KernelKGC31M23

end
