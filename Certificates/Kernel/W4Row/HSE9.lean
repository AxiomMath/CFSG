module

public import Certificates.Kernel.W4Row.HSE9K
public import Certificates.Kernel.LocalQT.SV.C4126
public import CFSG.Certificates.Kernel.W4Row.EPackKSound

public section

namespace CFSG.KD.W4E.HSE9

open CFSG.KC.LQT.TC CFSG.KC.W4E CFSG.KC.IntLines CFSG.KC.LQT.Cov
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

theorem parse {s : String} (hs : s.toList ∈ strsC) :
    CFSG.Quasithin.B45Exc.Tab.parseInts s = lineInts s.toList :=
  parseInts_str (List.all_eq_true.1 strs _ hs)

theorem check : hsE9Check = true := by
  unfold hsE9Check hsWordP hsE9WX hsE9WY hsE9WM1 hsE9WM2 hsE9WM3 hsE9WK hsE9WH5 hsE9WH12
    hsE9WH21 hsE9WH34
  rw [parse (s := hsE9WXStr) (by simp [strsC]), parse (s := hsE9WYStr) (by simp [strsC]),
    parse (s := hsE9WM1Str) (by simp [strsC]), parse (s := hsE9WM2Str) (by simp [strsC]),
    parse (s := hsE9WM3Str) (by simp [strsC]), parse (s := hsE9WKStr) (by simp [strsC]),
    parse (s := hsE9WH5Str) (by simp [strsC]), parse (s := hsE9WH12Str) (by simp [strsC]),
    parse (s := hsE9WH21Str) (by simp [strsC]), parse (s := hsE9WH34Str) (by simp [strsC]),
    CFSG.KD.LQT.C4126.gens_eq, CFSG.KD.LQT.C4126.tp_eq (k := 5) (by norm_num),
    CFSG.KD.LQT.C4126.tp_eq (k := 12) (by norm_num), CFSG.KD.LQT.C4126.tp_eq (k := 21) (by norm_num),
    CFSG.KD.LQT.C4126.tp_eq (k := 34) (by norm_num)]
  obtain ⟨h1, h2⟩ := e9Full_of pack
  simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true] at h2 ⊢
  exact ⟨⟨⟨⟨h1, h2.1⟩, h2.2.1⟩, h2.2.2.1⟩, h2.2.2.2⟩

end CFSG.KD.W4E.HSE9

end
