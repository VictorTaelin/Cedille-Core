// A context is an array of (name, type) tiples
class Context {
  constructor(binds) {
    this.binds = binds;
  }

  // Shifts all elements of the context
  shift(depth, inc) {
    var binds = [];
    for (var binder of this.binds) {  
      if (binder == null) {
        binds.push(null);
      } else {
        binds.push([binder[0], binder[1].shift(depth, inc)]);
      }
    }
    return new Context(binds);
  }

  // Extends the context with a term, shifting accourdingly
  extend([name, term]) {
    return new Context([[name, term ? term.shift(0, 1) : new Var(0)]].concat(this.shift(0, 1).binds));
  }

  // Returns the type of an element given its index
  get_type(index) {
    if (index < this.binds.length) {
      return this.binds[index][1];
    }
  }

  // Returns the name of an element given its index,
  // avoiding capture by appending 's if needed
  get_name(index) {
    if (index < this.binds.length) {
      var name = this.binds[index][0];
      for (var i = 0; i < index; ++i) {
        if (this.binds[i][0] === this.binds[index][0]) {
          name += "'";
        }
      }
      return name;
    }
  }

  // Finds a term by its name, skipping a number of terms
  // (this allows the x''' syntax be used to address shadowed vars)
  find_by_name(find_name, skip) {
    for (var [name, term] of this.binds) {
      if (find_name === name) {
        if (skip > 0) {
          skip -= 1;
        } else {
          return [name, term];
        }
      }
    }
    return null;
  }

  // Pretty prints a context
  show() {
    if (this.binds.length === 0) {
      return "(empty)\n";
    } else {
      var text = "";
      for (var [name, value] of this.binds.slice(0).reverse()) {
        text += "-- " + name + " : " + value.to_string(this) + "\n";
      }
      return text;
    }
  }

  // Formats a type-mismatch error message
  show_mismatch(expect, actual, value) {
      var text = "";
      text += "ERROR: Type mismatch on " + value + ".\n";
      text += "- Expect: " + expect.eval(true).to_string(this) + "\n";
      text += "- Actual: " + actual.eval(true).to_string(this) + "\n"
      text += "- Context:\n" 
      text += this.show();
      return text;
  }
}

// A reference to a term. This is used to preserve names and cache types.
class Ref {
  constructor(name, term, clos) {
    this.name = name; // String
    this.term = term; // Term
    this.clos = clos; // Bool
    this.type = null; // Maybe Term
  }

  to_string(context = new Context([])) {
    return this.name;
  }

  shift(depth, inc) {
    return this.clos ? this : new Ref(this.name, this.term.shift(depth, inc));
  }

  subst(depth, val) {
    return this.clos ? this : new Ref(this.name, this.term.subst(depth, val));
  }

  equal(other) {
    return this.term.equal(other);
  }

  eval(except_bind) {
    return this.term.eval(except_bind);
  }

  check(context = new Context([])) {
    if (!this.type) {
      this.type = this.term.check(context);
    }
    return this.type;
  }
}

// The type of types (TODO: kinding system, right now we have Type : Type)
// Syntax: Type
class Typ {
  constructor() {
  }

  to_string() {
    return "Type";
  }

  shift(depth, inc) {
    return new Typ();
  }

  subst(depth, val) {
    return new Typ();
  }

  equal(other) {
    return other instanceof Typ;
  }

  eval(except_bind) {
    return new Typ();
  }
  
  check(context = new Context([])) {
    return new Typ();
  }
}

// The type of a lambda (either erased or not)
// Syntax: {x : A} B
class All {
  constructor(eras, name, bind, body) {
    this.eras = eras; // Bool (true if erased)
    this.name = name; // String (argument name)
    this.bind = bind; // Term (argument type)
    this.body = body; // Term (function body)
  }

  to_string(context = new Context([])) {
    var eras = this.eras ? "-" : "";
    var name = this.name;
    var bind = " : " + this.bind.to_string(context);
    var body = this.body.to_string(context.extend([this.name, this.bind]));
    return "{" + eras + name + bind + "} " + body;
  }

  shift(depth, inc) {
    var eras = this.eras;
    var name = this.name;
    var bind = this.bind.shift(depth, inc);
    var body = this.body.shift(depth + 1, inc);
    return new All(eras, name, bind, body);
  }

  subst(depth, val) {
    var eras = this.eras;
    var name = this.name;
    var bind = this.bind.subst(depth, val);
    var body = this.body.subst(depth + 1, val && val.shift(0, 1));
    return new All(eras, name, bind, body);
  }

  equal(other) {
    if (other instanceof All) {
      var eras = this.eras == other.eras;
      var bind = this.bind.equal(other.bind);
      var body = this.body.equal(other.body);
      return eras && bind && body;
    }
    return false;
  }

  eval(except_bind) {
    var eras = this.eras;
    var name = this.name;
    var bind = except_bind ? this.bind : this.bind.eval(except_bind);
    var body = this.body.eval(except_bind);
    return new All(eras, name, bind, body);
  }

  check(context = new Context([])) {
    var bind_v = this.bind;
    var bind_t = this.bind.check(context);
    var body_t = this.body.check(context.extend([this.name, bind_v]));
    if (!bind_t.eval(false).equal(new Typ()) || !body_t.eval(false).equal(new Typ())) {
      throw "Forall not a type: " + this.to_string(context) + "\n- Context:\n" + context.show();
    }
    return new Typ();
  }
}

// A lambda (either erased or not)
// Syntax: [x : A] t
class Lam {
  constructor(eras, name, bind, body) {
    this.eras = eras; // Bool (true if erased)
    this.name = name; // String (argument name)
    this.bind = bind; // Term (argument type)
    this.body = body; // Term (function body)
  }

  to_string(context = new Context([])) {
    var eras = this.eras ? "-" : "";
    var name = this.name;
    var bind = this.bind ? " : " + this.bind.to_string(context) : "";
    var body = this.body.to_string(context.extend([this.name, null]));
    return "[" + eras + name + bind + "] " + body;
  }

  shift(depth, inc) {
    var eras = this.eras;
    var name = this.name;
    var bind = this.bind && this.bind.shift(depth, inc);
    var body = this.body.shift(depth + 1, inc);
    return new Lam(eras, name, bind, body);
  }

  subst(depth, val) {
    var eras = this.eras;
    var name = this.name;
    var bind = this.bind && this.bind.subst(depth, val);
    var body = this.body.subst(depth + 1, val && val.shift(0, 1));
    return new Lam(eras, name, bind, body);
  }

  equal(other) {
    if (other instanceof Lam) {
      var eras = this.eras === other.eras;
      var body = this.body.equal(other.body);
      return eras && body;
    }
    return false;
  }

  eval(except_bind) {
    if (this.eras) {
      return this.body.eval(except_bind).subst(0, null);
    } else {
      var eras = this.eras;
      var name = this.name;
      var bind = null;
      var body = this.body.eval(except_bind);
      return new Lam(eras, name, bind, body);
    }
  }

  check(context = new Context([])) {
    if (this.bind === null) {
      throw "Can't infer non-annotated lambda. Context:" + context.show();
    } else {
      var bind_v = this.bind;
      var bind_t = this.bind.check(context);
      var body_t = this.body.check(context.extend([this.name, bind_v]));
      if (!bind_t.eval(false).equal(new Typ())) {
        throw "Function type not a type. Context:" + context.show();
      }
      return new All(this.eras, this.name, bind_v, body_t);
    }
  }
}

// An application
// Syntax: (f x y z ...)
class App {
  constructor(eras, func, argm) {
    this.eras = eras; // Bool (true if erased)
    this.func = func; // Term (the function)
    this.argm = argm; // Term (the argument)
  }

  to_string(context = new Context([])) {
    var text = ")";
    var self = this;
    while (self instanceof App) {
      text = " " + (self.eras ? "-" : "") + (self.argm?self.argm.to_string(context):"???") + text;
      self = self.func;
    }
    return "(" + self.to_string(context) + text;
  }

  shift(depth, inc) {
    var eras = this.eras;
    var func = this.func.shift(depth, inc);
    var argm = this.argm.shift(depth, inc);
    return new App(eras, func, argm);
  }

  subst(depth, val) {
    var eras = this.eras;
    var func = this.func.subst(depth, val);
    var argm = this.argm.subst(depth, val);
    return new App(eras, func, argm);
  }

  equal(other) {
    if (other instanceof App) { 
      var eras = this.eras == other.eras;
      var func = this.func.equal(other.func);
      var argm = this.argm.equal(other.argm);
      return eras && func && argm;
    }
    return false;
  }

  eval(except_bind) {
    if (this.eras) {
      return this.func.eval(except_bind);
    } else {
      var func_v = this.func.eval(except_bind);
      if (!(func_v instanceof Lam)) {
        return new App(this.eras, func_v, this.argm.eval(except_bind));
      } else {
        return func_v.body.subst(0, this.argm).eval(except_bind);
      }
    }
  }

  check(context = new Context([])) {
    var func_t = this.func.check(context).eval(true);
    var argm_t = this.argm.check(context);
    var expect = func_t.bind;
    var actual = argm_t;
    if (!(func_t instanceof All)) {
      throw "Non-function application on `" + this.to_string(context) + "`.\n- Context:\n" + context.show();
    }
    if (func_t.eras !== this.eras) {
      throw "Mismatched erasure on " + this.to_string(context) + ".";
    }
    if (!expect.eval(false).equal(actual.eval(false))) {
      throw context.show_mismatch(expect, actual, "application: " + this.to_string(context));
    }
    return func_t.body.subst(0, this.argm);
  }
}

// A bruijn-indexed variable
// Syntax: (a string representing its name)
class Var {
  constructor(index) {
    this.index = index; // Number
  }

  to_string(context = new Context([])) {
    return context.get_name(this.index) || "#" + this.index;
  }

  shift(depth, inc) {
    return new Var(this.index < depth ? this.index : this.index + inc);
  }

  subst(depth, val) {
    if (depth === this.index) {
      if (val === null) {
        throw "Use of erased variable.";
      } else {
        return val;
      }
    }
    return new Var(this.index - (this.index > depth ? 1 : 0));
  }

  equal(other) {
    return other instanceof Var && this.index === other.index;
  }

  eval(except_bind) {
    return new Var(this.index);
  }

  check(context = new Context([])) {
    return context.get_type(this.index);
  }
}

// A dependent intersection between two types
// Syntax: <x : A> B
class Dep {
  constructor(name, typ0, typ1) {
    this.name = name; // String
    this.typ0 = typ0; // Term
    this.typ1 = typ1; // Term
  }

  to_string(context = new Context([])) {
    var name = this.name;
    var typ0 = this.typ0.to_string(context);
    var typ1 = this.typ1.to_string(context.extend([name, null]));
    return "<" + name + " : " + typ0 + "> " + typ1;
  }

  shift(depth, inc) {
    var name = this.name;
    var typ0 = this.typ0.shift(depth, inc);
    var typ1 = this.typ1.shift(depth + 1, inc);
    return new Dep(name, typ0, typ1);
  }

  subst(depth, val) {
    var name = this.name;
    var typ0 = this.typ0.subst(depth, val);
    var typ1 = this.typ1.subst(depth + 1, val && val.shift(0, 1));
    return new Dep(name, typ0, typ1);
  }

  equal(other) {
    if (other instanceof Dep) {
      var typ0 = this.typ0.equal(other.typ0)
      var typ1 = this.typ1.equal(other.typ1);
      return typ0 && typ1;
    }
    return false;
  }

  eval(except_bind) {
    var name = this.name;
    var typ0 = this.typ0.eval(except_bind);
    var typ1 = this.typ1.eval(except_bind);
    return new Dep(name, typ0, typ1);
  }

  check(context = new Context([])) {
    var typ0_t = this.typ0.check(context);
    var typ1_t = this.typ1.check(context.extend([this.name, this.typ0]));
    if (!typ0_t.eval(false).equal(new Typ()) || !typ0_t.eval(false).equal(typ1_t.eval(false))) {
      throw "Dependent intersection not a type. Context: " + context.show();
    }
    return new Typ();
  }
}

// The value of a dependent intersection
// Syntax: @T = a & b
class New {
  constructor(type, val0, val1) {
    this.type = type;
    this.val0 = val0;
    this.val1 = val1;
  }

  to_string(context = new Context([])) {
    var type = this.type.to_string(context);
    var val0 = this.val0.to_string(context);
    var val1 = this.val1.to_string(context);
    return ":" + type + " = " + val0 + " & " + val1;
  }

  shift(depth, inc) {
    var type = this.type.shift(depth, inc);
    var val0 = this.val0.shift(depth, inc);
    var val1 = this.val1.shift(depth, inc);
    return new New(type, val0, val1);
  }

  subst(depth, val) {
    var type = this.type.subst(depth, val);
    var val0 = this.val0.subst(depth, val);
    var val1 = this.val1.subst(depth, val);
    return new New(type, val0, val1);
  }

  equal(other) {
    return this.val0.equal(other);
  }

  eval(except_bind) {
    return this.val0.eval(except_bind);
  }
  
  check(context = new Context([])) {
    var type_v = this.type.eval(false);
    if (!(type_v instanceof Dep)) {
      throw ("Invalid instantiation: `" + this.to_string(context) + "`.\n"
          + "Its type must be a dependent intersection `<x : A> B`.");
    }
    var expect = type_v.typ0;
    var actual = this.val0.check(context);
    if (!expect.eval(false).equal(actual.eval(false))) {
      throw context.show_mismatch(expect, actual, "first value of intersection: `" + this.to_string(context) + "`");
    }
    var expect = type_v.typ1.subst(0, this.val0);
    var actual = this.val1.check(context);
    if (!expect.eval(false).equal(actual.eval(false))) {
      throw context.show_mismatch(expect, actual, "second value of intersection: `" + this.to_string(context) + "`");
    }
    if (!this.val0.eval(false).equal(this.val1.eval(false))) {
      throw ("Non-equal values on intersection: `" + this.to_string(context) + "`.\n"
        + "- " + this.val0.eval(false).to_string(context) + "\n"
        + "- " + this.val1.eval(false).to_string(context));
    }
    return type_v;
  }
}

// The first projection of a dependent intersection
// Syntax: .x
class Fst {
  constructor(term) {
    this.term = term;
  }

  to_string(context = new Context([])) {
    return "." + this.term.to_string(context);
  }

  shift(depth, inc) {
    return new Fst(this.term.shift(depth, inc));
  }

  subst(depth, val) {
    return new Fst(this.term.subst(depth, val));
  }

  equal(other) {
    return this.term.equal(other);
  }

  eval(except_bind) {
    return this.term.eval(except_bind);
  }

  check(context = new Context([])) {
    var term_t = this.term.check(context).eval(true);
    if (!(term_t.eval(false) instanceof Dep)) {
      throw "The term " + this.to_string(context) + " isn't a dependent intersection.";
    }
    return term_t.typ0;
  }
}

// The second projection of a dependent intersection
// Syntax: +x
class Snd {
  constructor(term) {
    this.term = term;
  }

  to_string(context = new Context([])) {
    return "+" + this.term.to_string(context);
  }

  shift(depth, inc) {
    return new Snd(this.term.shift(depth, inc));
  }

  subst(depth, val) {
    return new Snd(this.term.subst(depth, val));
  }

  equal(other) {
    return this.term.equal(other);
  }

  eval(except_bind) {
    return this.term.eval(except_bind);
  }

  check(context = new Context([])) {
    var term_t = this.term.check(context).eval(true);
    if (!(term_t instanceof Dep)) {
      throw "The term " + this.to_string(context) + " isn't a dependent intersection.";
    }
    return term_t.typ1.subst(0, this.term);
  }
}

// Heterogeneous equality type
// Syntax: |a = b|
class Eql {
  constructor(val0, val1) {
    this.val0 = val0;
    this.val1 = val1;
  }

  to_string(context = new Context([])) {
    var val0 = this.val0.to_string(context);
    var val1 = this.val1.to_string(context);
    return "|" + val0 + " = " + val1 + "|";
  }

  shift(depth, inc) {
    var val0 = this.val0.shift(depth, inc);
    var val1 = this.val1.shift(depth, inc);
    return new Eql(val0, val1);
  }

  subst(depth, val) {
    var val0 = this.val0.subst(depth, val);
    var val1 = this.val1.subst(depth, val);
    return new Eql(val0, val1);
  }

  equal(other) {
    if (other instanceof Eql) { 
      var val0 = this.val0.equal(other.val0);
      var val1 = this.val1.equal(other.val1);
      return val0 && val1;
    }
    return false;
  }

  eval(except_bind) {
    var val0 = this.val0.eval(except_bind);
    var val1 = this.val1.eval(except_bind);
    return new Eql(val0, val1);
  }

  check(context = new Context([])) {
    return new Typ();
  }
}

// Equality reflexivity of term `t`, erasing to `k`
// Syntax: $t k
class Rfl {
  constructor(term, eras) {
    this.term = term;
    this.eras = eras;
  }

  to_string(context = new Context([])) {
    var term = this.term.to_string(context);
    var eras = this.eras.to_string(context);
    return "$" + term + " " + eras;
  }

  shift(depth, inc) {
    var term = this.term.shift(depth, inc);
    var eras = this.eras.shift(depth, inc);
    return new Rfl(term, eras);
  }

  subst(depth, val) {
    var term = this.term.subst(depth, val);
    var eras = this.eras.subst(depth, val);
    return new Rfl(term, eras);
  }

  equal(other) {
    return this.eras.equal(other);
  }

  eval(except_bind) {
    return this.eras.eval(except_bind);
  }

  check(context = new Context([])) {
    return new Eql(this.term, this.term);
  }
}

// Symmetry of equality
// Syntax: ~e
class Sym {
  constructor(iseq) {
    this.iseq = iseq;
  }

  to_string(context = new Context([])) {
    var iseq = this.iseq.to_string(context);
    return "~" + iseq;
  }

  shift(depth, inc) {
    var iseq = this.iseq.shift(depth, inc);
    return new Sym(iseq);
  }

  subst(depth, val) {
    var iseq = this.iseq.subst(depth, val);
    return new Sym(iseq);
  }

  equal(other) {
    return this.iseq.equal(other);
  }

  eval(except_bind) {
    return this.iseq.eval(except_bind);
  }

  check(context = new Context([])) {
    var iseq_t = this.iseq.check(context).eval(true);
    if (!(iseq_t instanceof Eql)) {
      throw "Non-equality symmetry: " + this.to_string() + "."
    }
    return new Eql(iseq_t.val1, iseq_t.val0);
  }
}

// Type-guided rewritting (allows replacing equal terms in types)
// Syntax: %x (P x) e t
class Rwt {
  constructor(name, type, iseq, term) {
    this.name = name;
    this.type = type;
    this.iseq = iseq;
    this.term = term;
  }

  to_string(context = new Context([])) {
    var name = this.name;
    var type = this.type.to_string(context.extend([name, null]));
    var iseq = this.iseq.to_string(context);
    var term = this.term.to_string(context);
    return "%" + name + " " + type + " " + iseq + " " + term;
  }

  shift(depth, inc) {
    var name = this.name;
    var type = this.type.shift(depth + 1, inc);
    var iseq = this.iseq.shift(depth, inc);
    var term = this.term.shift(depth, inc);
    return new Rwt(name, type, iseq, term);
  }

  subst(depth, val) {
    var name = this.name;
    var type = this.type.subst(depth + 1, val && val.shift(0, 1));
    var iseq = this.iseq.subst(depth, val);
    var term = this.term.subst(depth, val);
    return new Rwt(name, type, iseq, term);
  }

  equal(other) {
    return this.term.iseq(other);
  }

  eval(except_bind) {
    return this.term.eval(except_bind);
  }

  check(context = new Context([])) {
    var iseq_t = this.iseq.check(context).eval(true);
    if (!(iseq_t instanceof Eql)) {
      throw "Non-equality rewrite: " + this.to_string(context) + ".";
    }
    var term_t = this.term.check(context);
    var expect = this.type.subst(0, iseq_t.val0);
    var actual = term_t;
    if (!actual.eval(false).equal(expect.eval(false))) {
      throw context.show_mismatch(expect, actual, "(" + this.to_string(context) + ") rewrite");
    }
    return this.type.subst(0, iseq_t.val1);
  }
}

// Type casting (if `a = b`, gives `b` the type of `a`)
// Syntax: ^e a b
class Cst {
  constructor(iseq, val0, val1) {
    this.iseq = iseq;
    this.val0 = val0;
    this.val1 = val1;
  }

  to_string(context = new Context([])) {
    var iseq = this.iseq.to_string(context);
    var val0 = this.val0.to_string(context);
    var val1 = this.val1.to_string(context);
    return "^" + is_eq + " " + val0 + " " + val1;
  }

  shift(depth, inc) {
    var iseq = this.iseq.shift(depth, inc);
    var val0 = this.val0.shift(depth, inc);
    var val1 = this.val1.shift(depth, inc);
    return new Cst(iseq, val0, val1);
  }

  subst(depth, val) {
    var iseq = this.iseq.subst(depth, val);
    var val0 = this.val0.subst(depth, val);
    var val1 = this.val1.subst(depth, val);
    return new Cst(iseq, val0, val1);
  }

  equal(other) {
    return this.val1.equal(other);
  }

  eval(except_bind) {
    return this.val1.eval(except_bind);
  }

  check(context = new Context([])) {
    var iseq_t = this.iseq.check(context);
    if (!(iseq_t instanceof Eql)) {
      throw "Non-equality cast: " + this.to_string() + ".";
    }
    var val0_t = this.val0.check(context);
    return val0_t;
  }
}

function parse(code) {
  var index = 0;

  function is_space(char) {
    return char === " " || char === "\t" || char === "\n";
  }

  function is_name_char(char) {
    return "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_".indexOf(char) !== -1;
  }

  function skip_spaces() {
    while (index < code.length && is_space(code[index])) {
      index += 1;
    }
    return index;
  }

  function match(string) {
    skip_spaces();
    var sliced = code.slice(index, index + string.length);
    if (sliced === string) {
      index += string.length;
      return true;
    }
    return false;
  }

  function error(text) {
    text += "This is the relevant code:\n\n<<<";
    text += code.slice(index - 64, index) + "<<<HERE>>>";
    text += code.slice(index, index + 64) + ">>>";
    throw text;
  }

  function parse_exact(string) {
    if (!match(string)) {
      error("Parse error, expected '" + string + "'.\n");
    }
  }

  function parse_name() {
    skip_spaces();
    var name = "";
    while (index < code.length && is_name_char(code[index])) {
      name = name + code[index];
      index += 1;
    }
    return name;
  }

  function parse_term(context) {
    // Comment
    if (match("--")) {
      while (index < code.length && code[index] !== "\n") {
        index += 1;
      }
      return parse_term(context);
    }

    // Application
    else if (match("(")) {
      var func = parse_term(context);
      while (index < code.length && !match(")")) {
        var eras = match("-");
        var argm = parse_term(context);
        var func = new App(eras, func, argm);
        skip_spaces();
      }
      return func;
    }

    // Type
    else if (match("Type")) {
      return new Typ();
    }

    // Forall
    else if (match("{")) {
      var eras = match("-");
      var name = parse_name();
      var skip = parse_exact(":");
      var bind = parse_term(context);
      var skip = parse_exact("}");
      var body = parse_term(context.extend([name, null]));
      return new All(eras, name, bind, body);
    }

    // Lambda
    else if (match("[")) {
      var eras = match("-");
      var name = parse_name();
      var bind = match(":") ? parse_term(context) : null;
      var skip = parse_exact("]");
      var body = parse_term(context.extend([name, null]));
      return new Lam(eras, name, bind, body);
    }

    // Dependent intersection type
    else if (match("<")) {
      var name = parse_name();
      var skip = parse_exact(":");
      var bind = parse_term(context);
      var skip = parse_exact(">");
      var body = parse_term(context.extend([name, null]));
      return new Dep(name, bind, body);
    }

    // Dependent intersection value
    else if (match(":")) {
      var type = parse_term(context);
      var skip = parse_exact("=");
      var val0 = parse_term(context);
      var skip = parse_exact("&");
      var val1 = parse_term(context);
      return new New(type, val0, val1);
    }

    // Dependent intersection erased view
    else if (match(".")) {
      var term = parse_term(context);
      return new Fst(term);
    }

    // Dependent intersection full view
    else if (match("+")) {
      var term = parse_term(context);
      return new Snd(term);
    }

    // Equality type
    else if (match("|")) {
      var val0 = parse_term(context);
      var skip = parse_exact("=");
      var val1 = parse_term(context);
      var skip = parse_exact("|");
      return new Eql(val0, val1);
    }

    // Equality reflexivity
    else if (match("$")) {
      var term = parse_term(context);
      var eras = parse_term(context);
      return new Rfl(term, eras);
    }

    // Equality symmetry
    else if (match("~")) {
      var term = parse_term(context);
      return new Sym(term);
    }

    // Equality rewrite
    else if (match("%")) {
      var name = parse_name();
      var type = parse_term(context.extend([name, null]));
      var iseq = parse_term(context); 
      var term = parse_term(context);
      return new Rwt(name, type, iseq, term);
    }

    // Equality casting
    else if (match("^")) {
      var iseq = parse_term(context);
      var val0 = parse_term(context)
      var val1 = parse_term(context)
      return new Cst(iseq, val0, val1);
    }

    // Definition
    else if (match("def")) {
      var name = parse_name();
      var term = parse_term(context);
      var body = parse_term(context.extend([name, new Ref(name, term, true)]));
      return body.shift(0, -1);
    }

    // Local definition
    else if (match("let")) {
      var name = parse_name();
      var term = parse_term(context);
      var body = parse_term(context.extend([name, new Ref(name, term, false)]));
      return body.shift(0, -1);
    }

    // Variable (named)
    else {
      var name = parse_name();
      var skip = 0;
      while (match("'")) {
        skip += 1;
      }
      var bind = context.find_by_name(name, skip);
      if (bind) {
        return bind[1];
      }
      error("Parse error, unbound variable '" + name + "'.\n");
    }
  }

  return parse_term(new Context([]));
}

module.exports = {Context, Ref, Typ, All, Lam, App, Var, Dep, New, Fst, Snd, Eql, Rfl, Sym, Rwt, Cst, parse};
