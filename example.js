var cedille = require(".");

var example = `
  -- Boolean type construction

  def CBool {-Bool : Type} {true : Bool} {fals : Bool} Bool
  def ctrue [-Bool : Type] [true : Bool] [fals : Bool] true
  def cfals [-Bool : Type] [true : Bool] [fals : Bool] fals

  def IBool [self : CBool] {-Bool : {b : CBool} Type} {true : (Bool ctrue)} {fals : (Bool cfals)} (Bool self)
  def itrue                [-Bool : {b : CBool} Type] [true : (Bool ctrue)] [fals : (Bool cfals)] true 
  def ifals                [-Bool : {b : CBool} Type] [true : (Bool ctrue)] [fals : (Bool cfals)] fals

  def Bool <self : CBool> (IBool self)
  def true @self : (IBool self) = ctrue & itrue
  def fals @self : (IBool self) = cfals & ifals

  -- Proof of reflexivity: ∀ b. |(b true false) = b|

  def bool_reflection [b : Bool]
    def motive [b : CBool]|(b true fals) = b|
    (+b -motive ($ctrue ctrue) ($cfals cfals))

  -- Induction principle

  def bool_induction [b : Bool]
    [-P : {b : Bool} Type]
    [T  : (P true)]
    [F  : (P fals)]
    def motive [b : CBool](P (b -Bool true fals))
    (%x (P x) (bool_reflection b) (+b -motive T F))

  bool_induction
`;

var term = cedille(example);
console.log("Input:\n" + term.to_string() + "\n");
console.log("Type:\n" + term.check().to_string() + "\n");
console.log("Normal:\n" + term.eval().to_string() + "\n");
