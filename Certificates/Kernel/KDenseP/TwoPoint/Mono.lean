
module

public import Certificates.Kernel.KDenseP.TwoPoint.Base
public import Certificates.Kernel.KDenseP.ReplayN
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.MonoAll
public import CFSG.Certificates.Kernel.KDense.Data.Checks
import Certificates.Kernel.KDenseP.MonoTabL
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.MonoEChk0
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.MonoEChk1
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.MonoEChk2
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.MonoEChk3

public section

namespace CertificateChecks.KernelKDenseP.TwoPoint

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CertificateChecks.KernelKDenseP.Axis

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.TPM.MT = true := by
  kd_monoTabL CFSG.KD.TPME t

theorem neg_monoPad : andB (netOK 10 (2 ^ (4 * 1024 + 768)))
    (notB (monoPadOK { CFSG.KD.TPM.MT.ents 0 with qn := 2 ^ (4 * 1024 + 768) })) = true := by
  decide +kernel

theorem data_okT : dataOKP CFSG.KD.KDF.F CFSG.KD.TPM.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

open Lean in
macro "kd_tpR% " pre:ident s0:term:max w:num : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  `(CFSG.KC.KDenseP.replay_sound (run := $(n "rn"))
      (chk := CFSG.KC.KDenseP.chunkOKN 4 2 5 CFSG.KD.KDF.F CFSG.KD.TPM.MT $(n "WL"))
      (fun S S' c h3 h4 => CFSG.KC.KDenseP.chunkOKN_loc S S' c h3 h4)
      (fun S c h => CFSG.KC.KDenseP.chunkOKN_prod S c h) (CH := $(n "CH")) (PR := $(n "PRf"))
      (GK := $(n "GKf")) (G := $(n "Gf")) (S0 := $s0) (w := $w) (ng := kd_count% $pre $(mkIdent `u))
      (by kd_allE $pre $(mkIdent `u)) (by quickRfl))

open Lean in
macro "kd_tp3% " pre:ident w?:(num)? : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  let (s0, w, lt) ← match w? with
    | some w => pure ((n "S0" : Term), w, ← `(fun x hx =>
        (CFSG.KC.KDenseP.rlS_lt (Nat.lt_of_lt_of_le hx (by decide))).trans
          (by interval_cases x <;> rfl)))
    | none => pure (← `(CFSG.KD.KDF.I), Syntax.mkNumLit "3",
        ← `(fun x hx => CFSG.KC.KDenseP.rlS_lt hx))
  `(tp3_sound data_okT _ _ $(n "weq") (WL := $(n "WL")) (fun _ => rfl)
      (S := CFSG.KC.KDenseP.rlS $(n "rn") $(n "CH") $(n "PRf") $s0 $w)
      $lt (CH := $(n "CH")) (IXf := $(n "IXf"))
      (CHI := $(n "CHI")) (fun _ => rfl) (nch := kd_count% $pre $(mkIdent `CH)) (nIX := kd_count% $pre $(mkIdent `IX))
      (IT := $(n "IT")) (kd_tpR% $pre $s0 $w) (by decide +kernel) (by quickRfl) (by decide +kernel)
      (by quickRfl))

open Lean in
macro "kd_tp3v% " pre:ident : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  `(tp3_valid data_okT _ _ $(n "weq") (WL := $(n "WL")) (fun _ => rfl) (S := CFSG.KC.KDenseP.rlS $(n "rn") $(n "CH") $(n "PRf") CFSG.KD.KDF.I 3)
      (fun x hx => CFSG.KC.KDenseP.rlS_lt hx) (CH := $(n "CH")) (IXf := $(n "IXf"))
      (CHI := $(n "CHI")) (fun _ => rfl) (nch := kd_count% $pre $(mkIdent `CH)) (nIX := kd_count% $pre $(mkIdent `IX))
      (IT := $(n "IT")) (kd_tpR% $pre CFSG.KD.KDF.I 3) (by decide +kernel) (by quickRfl) (by decide +kernel)
      (by quickRfl))

open Lean in
macro "kd_one% " pre:ident ws:term:max t:term:max : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  `(item5_cong data_okT $(n "weq") (WL := $(n "WL")) (fun _ => rfl) (S := CFSG.KC.KDenseP.rlS $(n "rn") $(n "CH") $(n "PRf") CFSG.KD.KDF.I 3)
      (fun x hx => CFSG.KC.KDenseP.rlS_lt hx) (CH := $(n "CH")) (IXf := $(n "IXf"))
      (CHI := $(n "CHI")) (fun _ => rfl) (nch := kd_count% $pre $(mkIdent `CH)) (nIX := kd_count% $pre $(mkIdent `IX))
      (IT := $(n "IT")) (kd_tpR% $pre CFSG.KD.KDF.I 3) (by decide +kernel) (by quickRfl) (by decide +kernel)
      (ws := $ws) (by quickRfl) $t (by decide) rfl)

open Lean in
macro "kd_axis% " pre:ident w:num p:term:max : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  `(axis_sound data_okT $p $(n "weq") (WL := $(n "WL")) (fun _ => rfl)
      (S := CFSG.KC.KDenseP.rlS $(n "rn") $(n "CH") $(n "PRf") $(n "S0") $w)
      (CH := $(n "CH")) (IXf := $(n "IXf")) (CHI := $(n "CHI")) (fun _ => rfl)
      (nch := kd_count% $pre $(mkIdent `CH)) (nIX := kd_count% $pre $(mkIdent `IX)) (IT := $(n "IT"))
      (kd_tpR% $pre $(n "S0") $w) (by decide +kernel) (by quickRfl)
      (by rw [CFSG.KC.KDenseP.rlS_lt (x := 0) (w := $w) (by decide)]; quickRfl)
      (by rw [CFSG.KC.KDenseP.rlS_lt (x := 1) (w := $w) (by decide)]; quickRfl)
      (by rw [CFSG.KC.KDenseP.rlS_lt (x := 2) (w := $w) (by decide),
        CFSG.KC.KDenseP.rlS_lt (x := 0) (w := $w) (by decide)]; rfl)
      (by decide +kernel) (by quickRfl))

end CertificateChecks.KernelKDenseP.TwoPoint

end
