module

public import Certificates.Kernel.LyBase.EvFacts
public import Certificates.Kernel.LyBase.Kind

public section

namespace CertificateChecks.KernelLyBase

open CertificateChecks.KernelLy CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.LyonsSims.LyFinal

theorem famRel_rfam (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
    (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat)) (hbc : RB5Bound) :
    ∀ r ∈ Rcore107 ++ modularLearned ++ dist2BWords, FamRel eEvCore trEvCore r := by
  intro r hr
  rcases List.mem_append.1 hr with hr' | hr'
  · have h := List.all_eq_true.1 core_kind r hr'
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
    rcases h with ((hb | hkk) | ⟨e, he, hre⟩) | ⟨ev, hev, hrev⟩
    · exact Or.inl ⟨(isBWord_iff r).1 hb, rfam_bword_eq_one hc hd hbc r hr hb⟩
    · exact Or.inr (Or.inl hkk)
    · exact Or.inr (Or.inr (Or.inl ⟨e, he, hre, eEvCore_holds hc hd hbc e he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ev, hev, hrev, trEvCore_holds hc hd hbc ev hev⟩))
  · obtain ⟨hb, h1⟩ := dist2BWords_eq_one hc hd hbc r hr'
    exact Or.inl ⟨(isBWord_iff r).1 hb, h1⟩

end CertificateChecks.KernelLyBase

end
