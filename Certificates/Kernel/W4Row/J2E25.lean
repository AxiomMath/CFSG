module

public import Certificates.Kernel.W4Row.J2E25K
public import Certificates.Kernel.LocalQT.SV.C4127
public import CFSG.Certificates.Kernel.W4Row.E25KSound

public section

namespace CFSG.KD.W4E.J2E25

open CFSG.KC.LQT.TC CFSG.KC.W4E CFSG.KC.IntLines CFSG.KC.LQT.Cov
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

theorem parse {s : String} (hs : s.toList ∈ strsC) :
    CFSG.Quasithin.B45Exc.Tab.parseInts s = lineInts s.toList :=
  parseInts_str (List.all_eq_true.1 strs _ hs)

theorem check : j2E25Check = true := by
  unfold j2E25Check j2WordP j2E25WMs j2E25WX j2E25WY j2E25WHA j2E25WHB j2E25WM0 j2E25WM1
    j2E25WM2 j2E25WM3 j2E25WM4 j2E25WM5 j2E25WM6 j2E25WM7 j2E25WM8 j2E25WM9 j2E25WM10 j2E25WM11
  rw [parse (s := j2E25WXStr) (by simp [strsC]), parse (s := j2E25WYStr) (by simp [strsC]),
    parse (s := j2E25WHAStr) (by simp [strsC]), parse (s := j2E25WHBStr) (by simp [strsC]),
    parse (s := j2E25WM0Str) (by simp [strsC]), parse (s := j2E25WM1Str) (by simp [strsC]),
    parse (s := j2E25WM2Str) (by simp [strsC]), parse (s := j2E25WM3Str) (by simp [strsC]),
    parse (s := j2E25WM4Str) (by simp [strsC]), parse (s := j2E25WM5Str) (by simp [strsC]),
    parse (s := j2E25WM6Str) (by simp [strsC]), parse (s := j2E25WM7Str) (by simp [strsC]),
    parse (s := j2E25WM8Str) (by simp [strsC]), parse (s := j2E25WM9Str) (by simp [strsC]),
    parse (s := j2E25WM10Str) (by simp [strsC]), parse (s := j2E25WM11Str) (by simp [strsC]),
    CFSG.KD.LQT.C4127.gens_eq, CFSG.KD.LQT.C4127.tp_eq (k := 17) (by norm_num),
    CFSG.KD.LQT.C4127.tp_eq (k := 31) (by norm_num), CFSG.KD.LQT.C4127.tp_eq (k := 9) (by norm_num),
    CFSG.KD.LQT.C4127.targ_eq, Bool.and_eq_true]
  exact ⟨ep2Pack_of pack, threeConj_of_mcP tc3⟩

end CFSG.KD.W4E.J2E25

end
