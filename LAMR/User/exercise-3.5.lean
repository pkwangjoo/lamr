import Mathlib.Data.Nat.Factorial.Basic


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

theorem insert_all_lemma:
  (insertAllPositions x xs).length = xs.length.succ :=
by
  induction xs with
  | nil =>
    simp[insertAllPositions]
  | cons x' xs'' ih =>
    simp[insertAllPositions, ih]

theorem insert_all_lemma1:
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


theorem insert_all_positions_is_n_plus_one_times_itself :
  List.length (insertAllPositions x ls) = ls.length.succ :=
  by
    simp[insert_all_lemma1, insert_all_lemma]

theorem elem_perm:
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
-- #eval Nat.factorial 3
theorem length_of_perms_l_is_factorial_l :
  (permutations ls).length = ls.length.factorial := by
  induction ls with
  | nil => rfl
  | cons x xs ih =>
    rw [permutations, List.flatMap, List.length_flatten]
    rw[List.length_cons, Nat.factorial]
    -- #print Function.comp
    have h : ∀ res ∈ permutations xs,
      (insertAllPositions x res).length = Nat.succ xs.length :=
      by
        intros  res h_res
        simp[insert_all_lemma]
        #check elem_perm xs res h_res
        exact elem_perm xs res h_res
    rw [List.map_map]
    #check Function.comp
    #check List.map_congr_left h
    have map_eq : List.map (List.length ∘ fun res => insertAllPositions x res) (permutations xs) =
              List.map (fun _ => xs.length.succ) (permutations xs) := by
                rw[List.map_inj_left]
                intros a h1
                have help : List.length a = List.length xs :=
                  by
                    exact elem_perm xs a h1
                -- #check help h
                rw[Function.comp]
                rw[insert_all_positions_is_n_plus_one_times_itself]
                simp [help]
    rw[map_eq]
    have aa : ∀ x ∈ permutations xs, Nat.succ (List.length x) = Nat.succ (List.length xs) :=
    by
      intros y hy
      simp[]
      #check elem_perm xs y hy
      exact elem_perm xs y hy
    #check List.map_const'
    rw[List.map_const']
    #check (List.map_congr_left aa)
    rw[ih]
    generalize xs.length.factorial = n
    induction n with
    | zero => simp[]
    | succ n' fds =>
      rw[List.replicate_succ]
      rw[List.sum_cons]
      simp[fds]
      rw[Nat.mul_add, Nat.mul_one, Nat.add_comm]
      done
