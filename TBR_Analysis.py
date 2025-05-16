import math
from lark import Lark, Tree, Token
from lark.visitors import Interpreter
import tkinter as tk
from tkinter import messagebox
import traceback

# --- Lark Grammar Definition ---
# Defines the grammar for a simple C-like language, including expressions,
# statements, functions, and control structures.
grammar = r"""
%import common.CNAME -> IDENTIFIER
%import common.NUMBER
%import common.WS
%ignore WS

// Punctuation and operators.
EQUAL: "="
SEMICOLON: ";"
COMMA: ","
LPAR: "("
RPAR: ")"
LBRACE: "{"
RBRACE: "}"
LT: "<"
GT: ">"
LE: "<="
GE: ">="
PLUS: "+"
MINUS: "-"
STAR: "*"
SLASH: "/"
ANDAND: "&&"
OROR: "||"
NOT: "!"
EQEQ: "=="
NE: "!="

// Start symbol.
start: external_declaration+

external_declaration: function_definition
                    | declaration

function_definition: declaration_specifiers declarator block

declaration: declaration_specifiers init_declarator_list? SEMICOLON

declaration_specifiers: "int" | "float" | "double" | "char" | "void"

init_declarator_list: init_declarator (COMMA init_declarator)*
init_declarator: declarator (EQUAL initializer)?
initializer: expr

declarator: IDENTIFIER ("(" parameter_list? ")")?
parameter_list: parameter_declaration (COMMA parameter_declaration)*
parameter_declaration: declaration_specifiers declarator?

block: LBRACE stmt* RBRACE

?stmt: if_stmt
     | while_stmt
     | for_stmt
     | compound_stmt
     | expression_statement
     | declaration
     | jump_stmt

compound_stmt: block
expression_statement: expr SEMICOLON
jump_stmt: "return" expr? SEMICOLON

if_stmt: "if" LPAR expr RPAR stmt ("else" stmt)? -> if_stmt
while_stmt: "while" LPAR expr RPAR stmt -> while_loop
for_stmt: "for" LPAR for_init? SEMICOLON for_cond? SEMICOLON for_iter? RPAR stmt -> for_loop

for_init: expr
for_cond: expr
for_iter: expr

assignment: IDENTIFIER EQUAL expr -> assign

?expr: assignment
     | expr PLUS additive -> add
     | expr MINUS additive -> subtract
     | expr LT additive -> less
     | expr GT additive -> greater
     | expr LE additive -> less_equal
     | expr GE additive -> greater_equal 
     | additive

?additive: multiplicative
         | additive STAR multiplicative -> multiply
         | additive SLASH multiplicative -> divide
         | multiplicative

?multiplicative: unary
                | multiplicative STAR unary -> multiply
                | multiplicative SLASH unary -> divide
                | unary

?unary: (PLUS | MINUS | NOT)? primary
      | "sin" LPAR expr RPAR -> sin
      | "cos" LPAR expr RPAR -> cos
      | "tan" LPAR expr RPAR -> tan

?primary: IDENTIFIER -> var
        | NUMBER -> number
        | LPAR expr RPAR

%import common.NUMBER
"""

# --- Interpreter for Dependency Tracking ---
class DebugDependencyInterpreter(Interpreter):
    """
    Traverses the parse tree to record data dependencies,
    overwritten variables, control flow events, and loop info.
    """

    def __init__(self):
        # Global environment stack for variable scopes
        self.env = {}
        self.scope_stack = [self.env]

        # Lists and maps to collect analysis data
        self.instructions = []          # All assignment instructions
        self.overwritten_deps = {}      # Records of overwritten variables
        self.loop_vars = set()          # Variables modified in loops
        self.operation_map = {}         # Map variable to operation type
        self.context_stack = []         # Tracks current control context
        self.global_index = 0           # Monotonic counter for instruction order
        self.debug = True               # Enable debug printing

        # Control flow tracking
        self.branch_info = []
        self.control_pushes = []
        self.loop_info = {}

    def debug_print(self, *args):
        # Conditional debug output
        if self.debug:
            print("[DEBUG]", *args)

    def current_context(self):
        # Return the current control context or default
        if self.context_stack:
            return self.context_stack[-1]
        return ("straight", None)

    def assign(self, tree):
        # Handle assignment nodes: record dependencies and pushes
        var_token = tree.children[0]
        expr = tree.children[2]
        var_name = str(var_token)

        # Update indices and context
        ctx_type, ctx_val = self.current_context()
        idx = getattr(var_token, "line", None)
        self.global_index += 1

        # Find all variables used on the right hand side
        flat_deps = self.find_dependencies(expr)

        # Remove self-dependency for simple add/subtract
        if isinstance(expr, Tree) and expr.data in ("add", "subtract"):
            flat_deps = [d for d in flat_deps if d != var_name]

        # Detect truly nonlinear multiply/divide (both operands non-constant)
        is_nonlinear_mul = False
        if isinstance(expr, Tree) and expr.data in ("multiply", "divide"):
            def is_constant(n):
                return (
                    isinstance(n, Token) and n.type == "NUMBER"
                ) or (
                    isinstance(n, Tree) and n.data == "number"
                )
            left, right = expr.children[0], expr.children[-1]
            if not (is_constant(left) or is_constant(right)):
                is_nonlinear_mul = True
            else:
                flat_deps = [d for d in flat_deps if d != var_name]

        # Determine if this assignment overwrites an existing variable
        is_overwrite = True

        # Look up previous dependencies if there is a self-dependency
        prev_deps = []
        if is_overwrite and var_name in flat_deps:
            prev_deps = (
                self.scope_stack[-1].get(var_name, [])
                or next((sc[var_name] for sc in reversed(self.scope_stack[:-1]) if var_name in sc), [])
            )

        # Decide if a PUSH message is needed at this kill-point
        push_vars = []
        if is_overwrite:
            if self.has_trig(expr):
                push_vars = [var_name]
            elif is_nonlinear_mul:
                push_vars = [var_name]
            elif var_name in flat_deps:
                push_vars = [var_name]

        # Record PUSH events for overwritten variables
        for pv in push_vars:
            rec = {
                "deps": prev_deps if pv == var_name else [],
                "index": idx,
                "context": self.current_context(),
                "push_var": pv,
                "always": True
            }
            if ctx_type in ("while", "for"):
                rec["loop"] = ctx_val
                rec["iteration"] = self.loop_info.get(ctx_val, {}).get("iterations")
            self.overwritten_deps.setdefault(var_name, []).append(rec)
            self.debug_print(f"Will PUSH '{pv}' at idx={idx}")

        # Update variable scope and instruction list
        self.scope_stack[-1][var_name] = flat_deps
        self.instructions.append({
            "target": var_name,
            "inputs": flat_deps,
            "index": idx,
            "context": self.current_context()
        })
        if ctx_type in ("while", "for"):
            self.loop_vars.add(var_name)

        # Record the operation type for later analysis
        self.operation_map[var_name] = (
            "nonlinear_mul" if is_nonlinear_mul
            else expr.data if isinstance(expr, Tree)
            else "simple"
        )
        return tree

    def has_trig(self, node):
        # Check if any sin/cos/tan call exists in the subtree
        if not isinstance(node, Tree):
            return False
        if node.data in ("sin", "cos", "tan"):
            return True
        return any(self.has_trig(child) for child in node.children if isinstance(child, Tree))

    def if_stmt(self, tree):
        # Process an if statement: record branch context and visits
        condition = tree.children[1]
        self.visit(condition)
        idx = self.global_index

        self.control_pushes.append(f"PUSH CONTROL: if-test at instr {idx}")
        # Visit then-branch
        self.context_stack.append(("if", idx))
        self.visit(tree.children[3])
        self.context_stack.pop()

        # Visit else-branch if present
        if len(tree.children) > 4:
            idx2 = self.global_index
            self.context_stack.append(("else", idx2))
            self.visit(tree.children[4])
            self.context_stack.pop()
        return tree

    def while_loop(self, tree):
        # Process a while loop: record loops and a single iteration
        loop_id = f"loop_{self.global_index}"
        self.loop_info[loop_id] = {"iterations": 0}
        self.control_pushes.append(f"PUSH CONTROL: enter-while {loop_id}")

        # Visit condition (collect deps) and body
        self.visit(tree.children[1])
        self.context_stack.append(("while", loop_id))
        self.visit(tree.children[3])
        self.context_stack.pop()

        # Simulate one iteration increment
        self.loop_info[loop_id]["iterations"] += 1
        self.global_index += 1
        return tree

    def for_loop(self, tree):
        # Process a for loop: record loop entry and one iteration
        self.visit(tree.children[3])  # Visit loop condition
        loop_id = f"loop_{self.global_index}"
        self.loop_info[loop_id] = {"iterations": 0}
        self.control_pushes.append(f"PUSH CONTROL: enter-for {loop_id}")

        # Visit loop body
        self.context_stack.append(("for", loop_id))
        self.visit(tree.children[-1])
        self.context_stack.pop()

        # Simulate one iteration increment
        self.loop_info[loop_id]["iterations"] += 1
        self.global_index += 1
        return tree

    def block(self, tree):
        # Visit each statement in a block
        for child in tree.children:
            self.visit(child)
        return tree

    def external_declaration(self, tree):
        # Visit declarations and definitions at top level
        for child in tree.children:
            self.visit(child)
        return tree

    def function_definition(self, tree):
        # Visit components of a function (specifiers, signature, body)
        for child in tree.children:
            self.visit(child)
        return tree

    def init_declarator(self, tree):
        # Ensure variable exists in scope, and handle initializer via assign()
        decl = tree.children[0]
        var_token = decl.children[0]
        var_name = str(var_token)
        if var_name not in self.scope_stack[-1]:
            self.scope_stack[-1][var_name] = []
        if len(tree.children) == 2:
            init_expr = tree.children[1].children[0]
            eq = Token('EQUAL', '=')
            fake_assign = Tree('assign', [var_token, eq, init_expr])
            self.assign(fake_assign)
        return tree

    def declarator(self, tree):
        # Record a declared variable in the current scope
        var_token = tree.children[0]
        var_name = str(var_token)
        if var_name not in self.scope_stack[-1]:
            self.scope_stack[-1][var_name] = []
        return tree

    def jump_stmt(self, tree):
        # Handle return statements
        for child in tree.children:
            self.visit(child)
        return tree

    # Expression visitors (return nodes unchanged)
    def add(self, tree): return tree
    def subtract(self, tree): return tree
    def multiply(self, tree): return tree
    def divide(self, tree): return tree
    def sin(self, tree): return tree
    def cos(self, tree): return tree
    def tan(self, tree): return tree
    def var(self, tree): return tree
    def number(self, tree): return tree

    def visit(self, node):
        # Override visit to handle non-Tree nodes
        if not isinstance(node, Tree):
            return node
        return super().visit(node)

    def __default__(self, tree):
        # Default handler: visit all child nodes
        for child in tree.children:
            if isinstance(child, Tree):
                self.visit(child)
        return tree

    def find_dependencies(self, tree):
        # Recursively collect variable names from a subtree
        deps = []
        if isinstance(tree, Token) and tree.type in {"IDENTIFIER", "VARIABLE"}:
            deps.append(str(tree))
        elif isinstance(tree, Tree):
            for child in tree.children:
                deps.extend(self.find_dependencies(child))
        return deps

    def detect_operation_type(self, tree):
        # Determine operation type for a subtree (e.g., trig or arithmetic)
        if isinstance(tree, Tree) and tree.data in {"sin", "cos", "tan", "add", "subtract", "multiply", "divide"}:
            return tree.data
        return "simple"

# --- Analysis Pipeline Functions ---
def build_dependencies_from_instructions(instructions):
    """
    Build a mapping of each variable to the list of inputs
    from the last instruction that assigned to it.
    """
    deps = {}
    for instr in reversed(instructions):
        var = instr.get("target")
        if var and var not in deps:
            deps[var] = instr.get("inputs", [])
    return deps


def compute_varied(dependencies, independent_vars):
    """
    Compute the set of variables that vary based on independent variables.
    """
    varied = set(independent_vars)
    changed = True
    while changed:
        changed = False
        for var, inputs in dependencies.items():
            if var not in varied and any(inp in varied for inp in inputs):
                varied.add(var)
                changed = True
    return varied


def compute_useful(dependencies, dependent_vars):
    """
    Compute the set of variables useful for computing dependent variables.
    """
    useful = set(dependent_vars)
    changed = True
    while changed:
        changed = False
        for var, inputs in dependencies.items():
            if var in useful and any(inp not in useful for inp in inputs):
                useful.update(inputs)
                changed = True
    return useful


def compute_adjU(active_vars, instructions):
    """
    Compute the set of variables needed for adjoint usage (adjU).
    """
    adjU = set()
    required = set(active_vars)
    for instr in reversed(instructions):
        tgt = instr.get("target")
        inputs = instr.get("inputs", [])
        if tgt in required:
            adjU.update(inputs)
            required.remove(tgt)
            required.update(inputs)
    return adjU


def tbr_analysis(instructions, adjU, overwritten_deps):
    """
    Perform backward trace reuse analysis to determine PUSH points.
    Returns formatted PUSH messages and remaining requirements.
    """
    Req = set(adjU)
    records = []
    for instr in reversed(instructions):
        tgt = instr.get("target")
        inputs = instr.get("inputs", [])
        Req |= set(inputs)
        for rec in overwritten_deps.get(tgt, []):
            if rec.get("index") == instr.get("index"):
                pv = rec.get("push_var")
                always = rec.get("always", False)
                if always or pv in Req:
                    records.append((rec["index"], pv, rec))
                    if not always:
                        Req.remove(pv)
        if tgt in Req:
            Req.remove(tgt)
    # Sort and format messages
    records.sort(key=lambda x: x[0])
    pushes = []
    for idx, pv, rec in records:
        ctype, _ = rec.get("context", ("straight", None))
        if ctype == "straight":
            msg = f"PUSH {pv} before line {idx}"
        elif ctype in ("if", "else"):
            msg = f"PUSH {pv} before line {idx} at {ctype}-branch entry"
        else:
            msg = f"PUSH {pv} before line {idx} at loop entry"
        pushes.append(msg)
    return pushes, Req

# --- Main Pipeline Function ---
def run_pipeline(code, independent_vars, dependent_vars):
    """
    Parse the code, interpret dependencies, and run analysis.
    Returns a summary string of the results.
    """
    try:
        # Parse source code into an AST
        parser = Lark(grammar, lexer='contextual', parser='lalr', start='start')
        tree = parser.parse(code)

        interpreter = DebugDependencyInterpreter()
        interpreter.visit(tree)

        # Collect instruction and dependency data
        instructions = interpreter.instructions
        dependencies = build_dependencies_from_instructions(instructions)
        overwritten_deps = dict(interpreter.overwritten_deps)

        # Compute varied, useful, active, and adjU sets
        varied = compute_varied(dependencies, independent_vars)
        useful = compute_useful(dependencies, dependent_vars)
        active = varied & useful
        # Include loop and branch vars as active
        for var, recs in overwritten_deps.items():
            if any(ctx in ('while', 'for', 'if', 'else') for ctx, _ in (r['context'] for r in recs)):
                active.add(var)
        adjU = compute_adjU(active, instructions)

        # Perform TBR and collect control pushes
        variable_pushes, required = tbr_analysis(instructions, adjU, overwritten_deps)
        control_pushes = interpreter.control_pushes

        # Format and return results
        return (
            f"Instructions: {instructions}\n"
            f"Dependencies: {dependencies}\n"
            f"Overwritten Dependencies: {overwritten_deps}\n"
            f"Varied Variables: {varied}\n"
            f"Useful Variables: {useful}\n"
            f"Active Variables: {active}\n"
            f"AdjU Variables: {adjU}\n"
            f"Required Variables: {required}\n"
            f"Variable PUSHes: {variable_pushes}\n"
            f"Control PUSHes: {control_pushes}\n"
        )
    except Exception as e:
        # Catch and display exceptions
        return f"Error during pipeline processing: {e}\n{traceback.format_exc()}"

# --- Tkinter GUI Integration ---

def run_analysis():
    """
    Retrieve user input from the GUI, run analysis pipeline,
    and display results in a popup.
    """
    code = code_text.get("1.0", tk.END).strip()
    indep = [v.strip() for v in independent_entry.get().split(",") if v.strip()]
    dep = [v.strip() for v in dependent_entry.get().split(",") if v.strip()]

    result = run_pipeline(code, indep, dep)
    messagebox.showinfo("TBR Analysis Results", result)

# Build and run the application window
root = tk.Tk()
root.title("TBR Analysis Tool")

# Code input area
tk.Label(root, text="Enter your code:").pack(padx=10, pady=(10, 0))
code_text = tk.Text(root, height=15, width=80)
code_text.pack(padx=10, pady=5)

# Independent variables input
tk.Label(root, text="Input Variables (comma-separated):").pack(padx=10, pady=(10, 0))
independent_entry = tk.Entry(root, width=80)
independent_entry.pack(padx=10, pady=5)

# Dependent variables input
tk.Label(root, text="Output Variables (comma-separated):").pack(padx=10, pady=(10, 0))
dependent_entry = tk.Entry(root, width=80)
dependent_entry.pack(padx=10, pady=5)

# Run button
tk.Button(root, text="Run Analysis", command=run_analysis).pack(padx=10, pady=10)

# Start the GUI event loop
root.mainloop()
