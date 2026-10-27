module

public import Certificates.Kernel.LyDce.CoverData

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 100
set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelLyDce

open CFSG.KC CFSG.KC.LyDce CertificateChecks.KernelLyB

theorem fix0_ok : fix0 = true := by decide +kernel

theorem root_key : Nat.beq (keyOf pk (maskOf o0)) (fldW 48 kp root) = true := by decide +kernel

theorem dfs_length : dfs.length = 16 := by decide +kernel

theorem o0_lt : o0.all (fun a => Nat.blt a 66825) = true := by decide +kernel

theorem sG_lt : sG.all (fun G => G.all fun g => (jwOf g).all fun j => Nat.blt j 6) = true := by
  decide +kernel

theorem rep_lt : rep.all (fun w => (jwOf w).all fun j => Nat.blt j 6) = true := by decide +kernel

theorem b_lt : (b1.all fun b => Nat.blt b 66825) = true ∧ (b2.all fun b => Nat.blt b 66825) = true :=
  ⟨by decide +kernel, by decide +kernel⟩

end CertificateChecks.KernelLyDce

end
