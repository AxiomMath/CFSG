module

public import Certificates.Kernel.TwoHSLe4.TFK
public import Certificates.Kernel.TwoHSLe4.TFData
public import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Raw

public section

namespace CertificateChecks.KernelTwoHSLe4.TF

open CFSG.EvenSporadicStandard.TwoHS

theorem ckq0 : eqLR q0R q0d = true := by quickRfl

theorem ckreps : eqLR repsR repsd = true := by quickRfl

theorem cksh : eqLR shatR shd = true := by quickRfl

theorem ckfR : eqLV fR fd = true := by quickRfl

theorem ckomR : eqLV omR omd = true := by quickRfl

theorem cktRV : rveq tRV tvd = true := by quickRfl

theorem cka1 : r4eq (toR4 alpha1) a1d = true := by quickRfl

theorem cka2 : r4eq (toR4 alpha2) a2d = true := by quickRfl

theorem ckvd : allL (fun v => memV v allVR) vd = true := by quickRfl

theorem hq0 : q0R = q0d := eqLR_eq _ _ ckq0

theorem hreps : repsR = repsd := eqLR_eq _ _ ckreps

theorem hsh : shatR = shd := eqLR_eq _ _ cksh

theorem hfR : fR = fd := eqLV_eq _ _ ckfR

theorem homR : omR = omd := eqLV_eq _ _ ckomR

theorem htRV : tRV = tvd := rveq_iff.1 cktRV

theorem ha1 : toR4 alpha1 = a1d := r4eq_iff.1 cka1

theorem ha2 : toR4 alpha2 = a2d := r4eq_iff.1 cka2

@[expose] def sLd (a : R4) : List R4 :=
  q0d ++ repsd.flatMap fun r => q0d.map fun q => rmul (rmul r a) q

@[expose] def siLd (ai : R4) : List R4 :=
  q0I ++ repsI.flatMap fun r => q0I.map fun q => rmul q (rmul ai r)

@[expose] def tLd (sl : List R4) : List R4 :=
  colR ((sl.filter fun a => fd.all fun v => rmv a v == v).flatMap fun c => shd.map fun s => rmul c s)

theorem S_eq (a : R4) : S a = sLd a := by
  change sListR a = _
  unfold sListR
  rw [hq0, hreps]
  rfl

theorem T_eq (a : R4) : T a = tLd (sLd a) := by
  rw [tLd, colR_eq, ← S_eq, ← hfR, ← hsh]
  rfl

end CertificateChecks.KernelTwoHSLe4.TF
