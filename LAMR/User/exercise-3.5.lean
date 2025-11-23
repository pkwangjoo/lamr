import Mathlib.Data.Nat.Factorial.Basic
set_option linter.unusedTactic false


def returnDivLessThanN (n: Nat) :=
  List.range n |> List.filter (fun i => n % i == 0)

#eval returnDivLessThanN (1000)



def isPerfect (n: Nat) :=
  n == List.sum (returnDivLessThanN n)

#eval returnDivLessThanN 6
#eval isPerfect 6

#eval List.range 10
def perfectNumbersLessThan1000 :=
  List.range 1000 |> List.filter isPerfect

#eval perfectNumbersLessThan1000


#eval [1,2,3] ++ [4,5]
def sublists : List Nat -> List (List Nat)
  | [] => [[]]
  | x :: xs' =>
    let res := sublists xs';

    res ++ (List.map (fun ls => x :: ls) res)


#eval sublists ([1,2,3])

theorem length_of_sublists_is_2_to_the_power_of_length_of_l :
    List.length (sublists ls) = 2 ^ (List.length ls) :=
  by
    induction ls with
    | nil =>
      simp[sublists]
    | cons x xs ih =>
      simp[sublists]
      rw[ih]
      rw[Nat.pow_add_one]
      -- #print Nat.mul_two
      rw[Nat.mul_two]


def insertAllPositions (el: Nat): List Nat → List (List Nat)
  | []      => [[el]]
  | x :: xs => (el :: x :: xs) :: (insertAllPositions el xs).map (fun zs => x :: zs)


#eval insertAllPositions 5 [1,2,3,4]

def permutations : List Nat -> List (List Nat)
  | [] => [[]]
  | x :: xs' =>
    let perms := permutations xs';
    perms.flatMap (fun res => insertAllPositions x res)

#eval permutations ([1,2,3,4]) |> List.length

lemma insert_all_lemma:
  (insertAllPositions x xs).length = xs.length.succ :=
by
  induction xs with
  | nil =>
    simp[insertAllPositions]
  | cons x' xs'' ih =>
    simp[insertAllPositions, ih]

lemma insert_all_lemma1:
  ∀a ∈ insertAllPositions x xs, a.length = xs.length.succ :=
by
  intros a
  induction xs generalizing a with
  | nil =>
    simp[insertAllPositions]
    intros h
    rw[h, List.length_singleton]
  | cons x xs' ih =>
    simp[insertAllPositions]
    aesop

lemma permuatation_preserves_length:
  ∀ xs a, a ∈ permutations xs -> a.length = xs.length :=
by
  intros xs
  induction xs with
  | nil =>
    rw[permutations]
    simp[]
  | cons x xs' ih =>
    intros a
    simp[permutations]
    intros xs'' h_xs''
    have helpful := (ih xs'' h_xs'')
    intros h_a_elem
    #check insert_all_lemma1 a h_a_elem
    simp [insert_all_lemma1 a h_a_elem]
    simp[helpful]

theorem length_of_perms_l_is_factorial_l :
  (permutations ls).length = ls.length.factorial :=
  by
  induction ls with
  | nil => rfl
  | cons x xs ih =>
    rw [permutations, List.flatMap, List.length_flatten]
    rw[List.length_cons, Nat.factorial]
    rw [List.map_map]
    have map_eq :
      List.map (List.length ∘ fun res => insertAllPositions x res) (permutations xs) =
      List.map (fun _ => xs.length.succ) (permutations xs) :=
    by
      rw[List.map_inj_left]
      intros perm ly
      rw[Function.comp]
      #check insert_all_lemma
      rw[insert_all_lemma, permuatation_preserves_length]
      exact ly
    rw[map_eq]
    rw[List.map_const']
    rw[ih]
    generalize xs.length.factorial = n
    induction n with
    | zero => simp[]
    | succ n' h_n' =>
      rw[List.replicate_succ]
      rw[List.sum_cons]
      simp[h_n']
      rw[Nat.mul_add, Nat.mul_one, Nat.add_comm]
      done
