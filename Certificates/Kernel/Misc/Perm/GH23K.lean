module

public import Certificates.Data.Kernel.Misc.PermGH23
public import Certificates.Data.GH23Data
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.Co1B.GenTri2045
public meta import Certificates.Kernel.Misc.Perm.GH23Gen

public section

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelMisc.GH23.E CFSG.KC.Misc.GH23Gen.eL
#kss_natlist CertificateChecks.KernelMisc.GH23.P CFSG.KC.Misc.GH23Gen.pL
#kss_natlist CertificateChecks.KernelMisc.GH23.S CFSG.KC.Misc.GH23Gen.sL
#kss_natlist CertificateChecks.KernelMisc.GH23.C CFSG.KC.Misc.GH23Gen.cL
#kss_natlist CertificateChecks.KernelMisc.GH23.NN CFSG.KC.Misc.GH23Gen.nL
#kss_natlist CertificateChecks.KernelMisc.GH23.NG CFSG.KC.Misc.GH23Gen.gnL
#kss_natlist CertificateChecks.KernelMisc.GH23.OF CFSG.KC.Misc.GH23Gen.oL
#kss_natlist CertificateChecks.KernelMisc.GH23.CO CFSG.KC.Misc.GH23Gen.coL
#kss_natlist CertificateChecks.KernelMisc.GH23.GT CFSG.KC.Misc.GH23Gen.gL

namespace CertificateChecks.KernelMisc.GH23

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.GH23 CFSG.OddStandard.SmallF3.HarrisU33.GH23Data

@[expose] noncomputable def gM (m j : Nat) : Nat := GT (Nat.add (Nat.mul 8 m) j)

@[expose] noncomputable def eM (m k : Nat) : Nat := E (Nat.add (OF m) k)

@[expose] noncomputable def pM (m k : Nat) : Nat := P (Nat.add (OF m) k)

@[expose] noncomputable def sM (m i : Nat) : Nat := S (Nat.add (OF m) i)

@[expose] noncomputable def cM (m i : Nat) : Nat := C (Nat.add (CO m) i)

@[expose] noncomputable def trR (m lo cnt : Nat) : Bool :=
  allR lo cnt (treeAt mul8 one8 (gM m) (NG m) (eM m) (pM m))

@[expose] noncomputable def srR (m lo cnt : Nat) : Bool := allR lo cnt (sortAt (NN m) (eM m) (sM m))

@[expose] noncomputable def clR (m lo cnt : Nat) : Bool :=
  allR lo cnt (closedAt mul8 (gM m) (NG m) (NN m) (eM m) (cM m))

@[expose] noncomputable def trB (m : Nat) : Bool := trR m 0 (NN m)

@[expose] noncomputable def srB (m : Nat) : Bool := srR m 0 (NN m)

@[expose] noncomputable def clB (m : Nat) : Bool := clR m 0 (NN m)

@[expose] noncomputable def aTB (q : Nat) : Bool := trR 40 (Nat.mul 2016 q) 2016

@[expose] noncomputable def aSB (q : Nat) : Bool := srR 40 (Nat.mul 2016 q) 2016

@[expose] noncomputable def aCB (q : Nat) : Bool := clR 40 (Nat.mul 2016 q) 2016

@[expose] noncomputable def qB (_ : Nat) : Bool := andB (trB 41) (andB (srB 41) (clB 41))

theorem gens_ok : ∀ m < 41, (members.getD m ⟨[], .top⟩).gens = (List.range (NG m)).map (gM m) := by
  decide +kernel

theorem q2_gens_ok : (List.range (NG 41)).map (gM 41) = q2gens := by decide +kernel

theorem sizes : (List.range 42).map NN = [5, 7, 10, 15, 20, 20, 20, 21, 30, 56, 56, 60, 60, 60, 60,
    60, 120, 120, 120, 120, 120, 120, 168, 168, 168, 168, 168, 180, 360, 360, 360, 360, 720, 720,
    720, 1344, 1344, 2520, 2520, 2520, 20160, 168] := by
  decide +kernel

end CertificateChecks.KernelMisc.GH23

#kc_slices CertificateChecks.KernelMisc.GH23.TK CertificateChecks.KernelMisc.GH23.trB 40
#kc_slices CertificateChecks.KernelMisc.GH23.SK CertificateChecks.KernelMisc.GH23.srB 40
#kc_slices CertificateChecks.KernelMisc.GH23.CK CertificateChecks.KernelMisc.GH23.clB 40
#kc_slices CertificateChecks.KernelMisc.GH23.ATK CertificateChecks.KernelMisc.GH23.aTB 10
#kc_slices CertificateChecks.KernelMisc.GH23.ASK CertificateChecks.KernelMisc.GH23.aSB 10
#kc_slices CertificateChecks.KernelMisc.GH23.ACK CertificateChecks.KernelMisc.GH23.aCB 10
#kc_slices CertificateChecks.KernelMisc.GH23.QK CertificateChecks.KernelMisc.GH23.qB 1

end
