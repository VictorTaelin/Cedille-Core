var cedille = require(".");

var example = `
  def the [-Unit : Type] [the : Unit] the

 -- Natural numbers

  def Nat
    {-Nat : Type}
    {succ : {x : Nat} Nat}
    {zero : Nat}
    Nat

  def succ
    [n    : Nat]
    [-Nat : Type]
    [succ : {x : Nat} Nat]
    [zero : Nat]
    (succ (n -Nat succ zero))

  def zero
    [-Nat : Type]
    [succ : {x : Nat} Nat]
    [zero : Nat]
    zero

  def n0 (the -Nat zero)
  def n1 (the -Nat (succ n0))
  def n2 (the -Nat (succ n1))
  def n3 (the -Nat (succ n2))
  def n4 (the -Nat (succ n3))

  -- Inductive hypothesis on natural numbers

  def Ind <self : Nat>
    {-Ind : {n : Nat} Type}
    {step : {-n : Nat} {i : (Ind n)} (Ind (succ n))}
    {base : (Ind zero)}
    (Ind self)

  def step [n : Ind] : Ind = (succ .n) &
    [-Ind : {n : Nat} Type]
    [step : {-n : Nat} {i : (Ind n)} (Ind (succ n))]
    [base : (Ind zero)]
    (step -.n (+n -Ind step base))

  def base : Ind = zero &
    [-Ind : {n : Nat} Type]
    [step : {-n : Nat} {i : (Ind n)} (Ind (succ n))]
    [base : (Ind zero)]
    base

  def to_ind [n : Nat] 
    (n -Ind step base)

  def i0 (to_ind n0)
  def i1 (to_ind n1)
  def i2 (to_ind n2)
  def i3 (to_ind n3)
  def i4 (to_ind n3)

  def ind_reflection [i : Ind]
    let motive [n : Nat]
      |.(to_ind n) = n|
    let case_s [-n : Nat] [i : |.(to_ind n) = n|]
      def cong [-A : Type] [-B : Type] [-x : A] [-y : A] [-e : |x = y|] [-f : {x : A} B]
        (%k |(f x) = (f k)| e ($(f x) [x] x))
      (cong -Nat -Nat -.(to_ind n) -n -i -succ)
    let case_z
      ($zero [x] x)
    (+i -motive case_s case_z)

  def ind_induction
    [i  : Ind]
    [-P : {i : Ind} Type]
    [S  : {-i : Ind} {ih : (P i)} (P (step i))]
    [Z  : (P base)]
    let motive [n : Nat]
      (P (to_ind n))
    let case_s [-n : Nat] [ih : (P (to_ind n))]
      (S -(to_ind n) ih)
    let case_z
      Z
    (%i (P i) (ind_reflection i) (+i -motive case_s case_z))

  ind_induction
`;

var term = cedille.parse(example);
console.log("Input:\n" + term.to_string() + "\n");
console.log("Type:\n" + term.check().to_string() + "\n");
console.log("Normal:\n" + term.eval().to_string() + "\n");
