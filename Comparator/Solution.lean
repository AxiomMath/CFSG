module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import CFSG.Certified.Classification

public section

universe u

theorem CFSGComparator.classification : TauCeti.ClassificationStatement.{u} :=
  TauCeti.classificationStatement_of_zero <|
    TauCeti.classificationStatement_iff.2 fun G _ _ _ =>
      CFSG.Certified.classification_finite_simple_groups G
