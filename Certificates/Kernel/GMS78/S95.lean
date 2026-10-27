module

public import Certificates.Kernel.GMS78.S16K
public import Certificates.Kernel.GMS78.S17Inv
public import Certificates.Kernel.GMS78.S17A
public import Certificates.Kernel.GMS78.S17C
public import Certificates.Kernel.GMS78.S17G0
public import Certificates.Kernel.GMS78.S17G1
public import Certificates.Kernel.GMS78.S17H0
public import Certificates.Kernel.GMS78.S17H1
public import Certificates.Kernel.GMS78.P117
public import CFSG.Certificates.Kernel.GMS78RuSSound
public import CFSG.Certificates.Kernel.GMS78RuSCentSound
public import CFSG.Certificates.Kernel.GMS78RuSGrpSound
public import CFSG.Certificates.Kernel.GMS78RuSCent16Sound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78.SD

open CFSG.KC.GMS CFSG.KLie.CT CFSG.GMS78RuS CertificateChecks.KernelGMS78.SK

theorem sTabs_false : sTabs gamArr dPartArr dCodeTab false GT DPR LIN DM DO0 := by
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := sTabs_true
  refine ⟨h1, h2, h3, h4, fun d _ e _ => ?_, h6⟩
  have e0 : DO0 = 0 := rfl
  rw [e0, Bool.false_and]
  simp [fget, Nat.zero_shiftRight] <;> rfl

theorem len_I160 : I160.length = 366 := by rfl

theorem len_I161 : I161.length = 366 := by rfl

theorem len_I170 : I170.length = 558 := by rfl

theorem len_I171 : I171.length = 558 := by rfl

theorem check16_eq (ε : Bool) : check16 ε = Gen.check16G gamArr dPartArr dCodeTab ε := rfl

theorem check17_eq (ε : Bool) : check17 ε = Gen.check17G gamArr dPartArr dCodeTab ε := rfl

theorem check16_false : check16 false = true := by
  rw [check16_eq]
  exact check16_sound gamArr dPartArr dCodeTab false GT DPR LIN DM DO0 I160 K160 sTabs_false
    (czListEq_eq j16f) (fun i hi => by
      rw [len_I160] at hi
      have := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) c16fB.all i hi
      rw [c16fF, neGet_eq, neGet_eq] at this
      exact kKey16_sound _ _ _ _ _ _ _ this) g16f

theorem check16_true : check16 true = true := by
  rw [check16_eq]
  exact check16_sound gamArr dPartArr dCodeTab true GT DPR LIN DM DO1 I161 K161 sTabs_true
    (czListEq_eq j16t) (fun i hi => by
      rw [len_I161] at hi
      have := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) c16tB.all i hi
      rw [c16tF, neGet_eq, neGet_eq] at this
      exact kKey16_sound _ _ _ _ _ _ _ this) g16t

theorem all17f : ∀ i < 558, kAll17 GT DPR LIN DM DO0 (neGet 0 I170 i) (neGet 0 K170 i) = true := by
  intro i hi
  rcases Nat.lt_or_ge i 279 with h | h
  · exact CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) a17fB0.all i h
  · have h2 : i - 279 < 279 := by omega
    have hG : ∀ g < 16, kGrpAt GT DPR LIN DM DO0 I170 K170 (neGet [] G17 g) = true :=
      fun g hg => CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) g17fB.all g hg
    have := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) a17fHB.all (i - 279) h2
    have e : Nat.add 279 (i - 279) = i := Nat.add_sub_of_le h
    rw [a17fH, e] at this
    exact SG.kAll17H_sound _ _ _ _ _ _ _ _ _ _ hG this

theorem all17t : ∀ i < 558, kAll17 GT DPR LIN DM DO1 (neGet 0 I171 i) (neGet 0 K171 i) = true := by
  intro i hi
  rcases Nat.lt_or_ge i 279 with h | h
  · exact CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) a17tB0.all i h
  · have h2 : i - 279 < 279 := by omega
    have hG : ∀ g < 16, kGrpAt GT DPR LIN DM DO1 I171 K171 (neGet [] G17 g) = true :=
      fun g hg => CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) g17tB.all g hg
    have := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) a17tHB.all (i - 279) h2
    have e : Nat.add 279 (i - 279) = i := Nat.add_sub_of_le h
    rw [a17tH, e] at this
    exact SG.kAll17H_sound _ _ _ _ _ _ _ _ _ _ hG this

theorem check17_false : check17 false = true := by
  rw [check17_eq]
  have hA : ∀ i < I170.length, kAll17 GT DPR LIN DM DO0 (I170.getD i 0) (K170.getD i 0) = true := by
    intro i hi
    rw [len_I170] at hi
    rw [← neGet_eq, ← neGet_eq]
    exact all17f i hi
  exact check17_sound gamArr dPartArr dCodeTab false GT DPR LIN DM DO0 I170 K170 sTabs_false
    (czListEq_eq i17f) (fun i hi => (kAll17_sound _ _ _ _ _ _ _ (hA i hi)).1)
    (fun i hi => (kAll17_sound _ _ _ _ _ _ _ (hA i hi)).2) f17f

theorem check17_true : check17 true = true := by
  rw [check17_eq]
  have hA : ∀ i < I171.length, kAll17 GT DPR LIN DM DO1 (I171.getD i 0) (K171.getD i 0) = true := by
    intro i hi
    rw [len_I171] at hi
    rw [← neGet_eq, ← neGet_eq]
    exact all17t i hi
  exact check17_sound gamArr dPartArr dCodeTab true GT DPR LIN DM DO1 I171 K171 sTabs_true
    (czListEq_eq i17t) (fun i hi => (kAll17_sound _ _ _ _ _ _ _ (hA i hi)).1)
    (fun i hi => (kAll17_sound _ _ _ _ _ _ _ (hA i hi)).2) f17t

end CertificateChecks.KernelGMS78.SD

end
