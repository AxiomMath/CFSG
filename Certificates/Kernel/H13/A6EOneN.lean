module

public import Certificates.Data.Kernel.A6EOneN
public import CFSG.Mathlib.Decide.Nodup
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.A6EOne
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore

public section

namespace CertificateChecks.A6EOneNK

open CFSG.Quasithin.H13.A6EOne CFSG.QuasithinUnique.A6Facts.Core

meta def autM : Array (Array Nat) := (autL.map List.toArray).toArray

end CertificateChecks.A6EOneNK

#kmisc_packarrs CertificateChecks.A6EOneNK.AP CertificateChecks.A6EOneNK.autM 4

namespace CertificateChecks.A6EOneNK

open CFSG.Quasithin.H13.A6EOne CFSG.QuasithinUnique.A6Facts.Core

set_option maxRecDepth 100000

theorem autL_eq : autL = (List.range 1440).map fun n => dec (AP n) := by decide +kernel

theorem coset : cosetOK = true := by decide +kernel

theorem g0XKeys :
    CFSG.Decide.bitsetNodup ((xList grp0.I).map (CFSG.Decide.listKey 10 [0, 1, 2, 3])) = true := by
  decide +kernel
theorem g0S : grp0.chkS = true := by decide +kernel
theorem g0Inv : grp0.chkInv = true := by decide +kernel
theorem g0Close : grp0.chkClose = true := by decide +kernel
theorem g0Cls : grp0.chkCls = true := by decide +kernel
theorem g0WitN : grp0.chkWitN (DofT AP) = true := by decide +kernel
theorem g0Words : grp0.chkWords = true := by decide +kernel

theorem g1XKeys :
    CFSG.Decide.bitsetNodup ((xList grp1.I).map (CFSG.Decide.listKey 10 [0, 1, 2, 3])) = true := by
  decide +kernel
theorem g1S : grp1.chkS = true := by decide +kernel
theorem g1Inv : grp1.chkInv = true := by decide +kernel
theorem g1Close : grp1.chkClose = true := by decide +kernel
theorem g1Cls : grp1.chkCls = true := by decide +kernel
theorem g1WitN : grp1.chkWitN (DofT AP) = true := by decide +kernel
theorem g1Words : grp1.chkWords = true := by decide +kernel

theorem g2XKeys :
    CFSG.Decide.bitsetNodup ((xList grp2.I).map (CFSG.Decide.listKey 10 [0, 1, 2, 3])) = true := by
  decide +kernel
theorem g2S : grp2.chkS = true := by decide +kernel
theorem g2Inv : grp2.chkInv = true := by decide +kernel
theorem g2Close : grp2.chkClose = true := by decide +kernel
theorem g2Cls : grp2.chkCls = true := by decide +kernel
theorem g2WitN : grp2.chkWitN (DofT AP) = true := by decide +kernel
theorem g2Words : grp2.chkWords = true := by decide +kernel

theorem g3XKeys :
    CFSG.Decide.bitsetNodup ((xList grp3.I).map (CFSG.Decide.listKey 10 [0, 1, 2, 3])) = true := by
  decide +kernel
theorem g3S : grp3.chkS = true := by decide +kernel
theorem g3Inv : grp3.chkInv = true := by decide +kernel
theorem g3Close : grp3.chkClose = true := by decide +kernel
theorem g3Cls : grp3.chkCls = true := by decide +kernel
theorem g3WitN : grp3.chkWitN (DofT AP) = true := by decide +kernel
theorem g3Words : grp3.chkWords = true := by decide +kernel

theorem g4XKeys :
    CFSG.Decide.bitsetNodup ((xList grp4.I).map (CFSG.Decide.listKey 10 [0, 1, 2, 3])) = true := by
  decide +kernel
theorem g4S : grp4.chkS = true := by decide +kernel
theorem g4Inv : grp4.chkInv = true := by decide +kernel
theorem g4Close : grp4.chkClose = true := by decide +kernel
theorem g4Cls : grp4.chkCls = true := by decide +kernel
theorem g4WitN : grp4.chkWitN (DofT AP) = true := by decide +kernel
theorem g4Words : grp4.chkWords = true := by decide +kernel

theorem g4WitN_neg :
    ({ grp4 with wit := grp4.wit.map fun w => { w with K := w.K.take 2 } } : Grp).chkWitN
      (DofT AP) = false := by
  decide +kernel

end CertificateChecks.A6EOneNK
