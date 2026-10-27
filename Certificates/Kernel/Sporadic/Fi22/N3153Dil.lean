module

public import CFSG.Certificates.Kernel.Fi22Snd.RowsW
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Lean
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import Mathlib.GroupTheory.Schreier

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.N3153

open Lean CFSG.KC.Eval in
meta def dilStep : Step := fun _ => do
  let mut outs : Array (Name × Val) := #[]
  for j in [0:12] do
    let e := 2 ^ j
    let B := 2 * e
    let mut H : Nat := 0
    for p in [0:4096] do
      if p / e % 2 == 1 then
        H := H ||| (1 <<< (p % B + 48 * B * (p / B)))
    outs := outs.push (Name.mkSimple s!"DH{e}", .nat H)
  return outs

end CertificateChecks.KernelSpor.N3153

#kc_eval CertificateChecks.KernelSpor N3153 CertificateChecks.KernelSpor.N3153.dilStep

namespace CertificateChecks.KernelSpor.N3153

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KC.Fi22Snd

@[expose] noncomputable def dilK (m : Nat) : Nat :=
  roundK DH1 (nat_lit 47) (roundK DH2 (nat_lit 94) (roundK DH4 (nat_lit 188)
    (roundK DH8 (nat_lit 376) (roundK DH16 (nat_lit 752) (roundK DH32 (nat_lit 1504)
    (roundK DH64 (nat_lit 3008) (roundK DH128 (nat_lit 6016) (roundK DH256 (nat_lit 12032)
    (roundK DH512 (nat_lit 24064) (roundK DH1024 (nat_lit 48128)
    (roundK DH2048 (nat_lit 96256) m)))))))))))

theorem mk2048 : allN 4096 (fun p =>
    Nat.beq (Nat.land (Nat.shiftRight DH2048 (posF 4096 p)) 1) (p / 2048 % 2)) = true := by quickRfl
theorem mk1024 : allN 4096 (fun p =>
    Nat.beq (Nat.land (Nat.shiftRight DH1024 (posF 2048 p)) 1) (p / 1024 % 2)) = true := by quickRfl
theorem mk512 : allN 4096 (fun p =>
    Nat.beq (Nat.land (Nat.shiftRight DH512 (posF 1024 p)) 1) (p / 512 % 2)) = true := by quickRfl
theorem mk256 : allN 4096 (fun p =>
    Nat.beq (Nat.land (Nat.shiftRight DH256 (posF 512 p)) 1) (p / 256 % 2)) = true := by quickRfl
theorem mk128 : allN 4096 (fun p =>
    Nat.beq (Nat.land (Nat.shiftRight DH128 (posF 256 p)) 1) (p / 128 % 2)) = true := by quickRfl
theorem mk64 : allN 4096 (fun p =>
    Nat.beq (Nat.land (Nat.shiftRight DH64 (posF 128 p)) 1) (p / 64 % 2)) = true := by quickRfl
theorem mk32 : allN 4096 (fun p =>
    Nat.beq (Nat.land (Nat.shiftRight DH32 (posF 64 p)) 1) (p / 32 % 2)) = true := by quickRfl
theorem mk16 : allN 4096 (fun p =>
    Nat.beq (Nat.land (Nat.shiftRight DH16 (posF 32 p)) 1) (p / 16 % 2)) = true := by quickRfl
theorem mk8 : allN 4096 (fun p =>
    Nat.beq (Nat.land (Nat.shiftRight DH8 (posF 16 p)) 1) (p / 8 % 2)) = true := by quickRfl
theorem mk4 : allN 4096 (fun p =>
    Nat.beq (Nat.land (Nat.shiftRight DH4 (posF 8 p)) 1) (p / 4 % 2)) = true := by quickRfl
theorem mk2 : allN 4096 (fun p =>
    Nat.beq (Nat.land (Nat.shiftRight DH2 (posF 4 p)) 1) (p / 2 % 2)) = true := by quickRfl
theorem mk1 : allN 4096 (fun p =>
    Nat.beq (Nat.land (Nat.shiftRight DH1 (posF 2 p)) 1) (p / 1 % 2)) = true := by quickRfl

theorem dilK_ok : DilOK dilK := by
  intro m hm q
  refine end_testBit ?_ q
  unfold dilK
  refine round_step (B := 2) (e := 1) (s := 47) ?_ mk1 (fun p => by
    unfold posF; constructor <;> intro h <;> omega)
  refine round_step (B := 4) (e := 2) (s := 94) ?_ mk2 (fun p => by
    unfold posF; constructor <;> intro h <;> omega)
  refine round_step (B := 8) (e := 4) (s := 188) ?_ mk4 (fun p => by
    unfold posF; constructor <;> intro h <;> omega)
  refine round_step (B := 16) (e := 8) (s := 376) ?_ mk8 (fun p => by
    unfold posF; constructor <;> intro h <;> omega)
  refine round_step (B := 32) (e := 16) (s := 752) ?_ mk16 (fun p => by
    unfold posF; constructor <;> intro h <;> omega)
  refine round_step (B := 64) (e := 32) (s := 1504) ?_ mk32 (fun p => by
    unfold posF; constructor <;> intro h <;> omega)
  refine round_step (B := 128) (e := 64) (s := 3008) ?_ mk64 (fun p => by
    unfold posF; constructor <;> intro h <;> omega)
  refine round_step (B := 256) (e := 128) (s := 6016) ?_ mk128 (fun p => by
    unfold posF; constructor <;> intro h <;> omega)
  refine round_step (B := 512) (e := 256) (s := 12032) ?_ mk256 (fun p => by
    unfold posF; constructor <;> intro h <;> omega)
  refine round_step (B := 1024) (e := 512) (s := 24064) ?_ mk512 (fun p => by
    unfold posF; constructor <;> intro h <;> omega)
  refine round_step (B := 2048) (e := 1024) (s := 48128) ?_ mk1024 (fun p => by
    unfold posF; constructor <;> intro h <;> omega)
  refine round_step (B := 4096) (e := 2048) (s := 96256) ?_ mk2048 (fun p => by
    unfold posF; constructor <;> intro h <;> omega)
  exact start_testBit hm

end CertificateChecks.KernelSpor.N3153

end
