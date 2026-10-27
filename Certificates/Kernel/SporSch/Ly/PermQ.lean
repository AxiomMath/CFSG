module

public import CFSG.Sporadic.Schreier.LyPermCheckInputs

public section

namespace CertificateChecks.KernelSporSch.LyPerm

open CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native

@[expose] def QStmt (a : Fin 11) : Prop := ∀ b c d : Fin 11,
    (∀ j : Fin 4, ∀ x, qCand a b c d (arrFun (qImgArr[j.val]!) x) =
      arrFun (qImgArr[j.val]!) (qCand a b c d x)) →
    (∀ x y, qCand a b c d x = qCand a b c d y → x = y) →
    ∃ m : Fin 12, ∀ x, qCand a b c d x = arrFun (qNaturalCentralizer[m.val]!) x

@[expose] def QStmt2 (a b : Fin 11) : Prop := ∀ c d : Fin 11,
    (∀ j : Fin 4, ∀ x, qCand a b c d (arrFun (qImgArr[j.val]!) x) =
      arrFun (qImgArr[j.val]!) (qCand a b c d x)) →
    (∀ x y, qCand a b c d x = qCand a b c d y → x = y) →
    ∃ m : Fin 12, ∀ x, qCand a b c d x = arrFun (qNaturalCentralizer[m.val]!) x

theorem qstmt_of {a : Fin 11} (h : ∀ b, QStmt2 a b) : QStmt a := fun b => h b

end CertificateChecks.KernelSporSch.LyPerm

end
