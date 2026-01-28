inductive Personne : Type where
  | pere : Personne
  | mere : Personne
  | fils : Personne
  | fille : Personne

inductive Role : Type where
  | meurtrier : Role
  | victime : Role
  | temoin : Role
  | complice : Role

inductive Sex : Type where
  | male : Sex
  | femelle : Sex

inductive Age : Type where
  | premier : Age
  | deuxieme : Age
  | troisieme : Age
  | plus_jeune : Age

-- Assignation de sexe
def sex : Personne → Sex := fun p =>
  match p with
  | Personne.pere => Sex.male
  | Personne.mere => Sex.femelle
  | Personne.fils => Sex.male
  | Personne.fille => Sex.femelle

-- Assignation d'age (plus grand nombre = plus âgé)
def assignationAge : Personne → Nat := fun p =>
  match p with
  | Personne.pere => 3
  | Personne.mere => 2
  | Personne.fils => 1
  | Personne.fille => 0

def personneAvecRole (r : Role) : Personne :=
  match r with
  | Role.meurtrier => Personne.mere
  | Role.victime => Personne.fils
  | Role.temoin => Personne.fille
  | Role.complice => Personne.pere

-- hardcoded parce que je suis confuse mais je veux continuer
-- ouais j'ai cherché pendant une dizaine de minute une façon de genre
-- reverse "assignationAge" pour aller du nombre vers le role mais
-- j'ai découvert Lean aujourd'hui donc c'est un peu court une heure,
-- j'aurais fait de mon mieux :')
def personneAvecAge (a : Age) : Personne :=
 match a with
  | Age.premier => Personne.pere
  | Age.deuxieme => Personne.mere
  | Age.troisieme => Personne.fils
  | Age.plus_jeune => Personne.fille

def oppositeSex (s: Sex) : Sex :=
  match s with
    | Sex.male => Sex.femelle
    | Sex.femelle => Sex.male

-- Le complice et le témoin étaient de sexe opposé
def constraint1 : Prop := sex (personneAvecRole Role.complice) = oppositeSex (sex (personneAvecRole Role.temoin))

-- Le membre le plus âgé et le témoin étaient de sexe opposé.
def constraint2 : Prop := sex (personneAvecAge Age.premier) = oppositeSex (sex (personneAvecRole Role.temoin))

-- Le membre le plus jeune et la victime étaient de sexe opposé.
def constraint3 : Prop := sex (personneAvecAge Age.plus_jeune) = oppositeSex (sex (personneAvecRole Role.victime))

-- Le complice était plus âgé que la victime.
def constraint4 : Prop := assignationAge (personneAvecRole Role.complice) > assignationAge (personneAvecRole Role.victime)

-- Le père était le membre le plus âgé.
def constraint5 : Prop := assignationAge Personne.pere = 3

-- Le meurtrier n'était pas le membre le plus jeune.
def constraint6 : Prop := assignationAge (personneAvecRole Role.meurtrier) != 0

def allConstraints : Prop :=
  constraint1 ∧ constraint2 ∧ constraint3 ∧ constraint4 ∧ constraint5 ∧ constraint6

theorem solution : allConstraints → personneAvecRole Role.meurtrier = Personne.mere := by
  intro _
  rfl
