#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <memory>
#include <queue>
#include <string.h>
#include <string>
#include <system_error>
#include <utility>
#include <vector>
#include <sstream>
#include <type_traits>

using namespace llvm;
using namespace llvm::sys;

FILE *pFile;

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns one of these for known things.
enum TOKEN_TYPE {

  IDENT = -1,        // [a-zA-Z_][a-zA-Z_0-9]*
  ASSIGN = int('='), // '='

  // delimiters
  LBRA = int('{'),  // left brace
  RBRA = int('}'),  // right brace
  LPAR = int('('),  // left parenthesis
  RPAR = int(')'),  // right parenthesis
  SC = int(';'),    // semicolon
  COMMA = int(','), // comma

  // types
  INT_TOK = -2,   // "int"
  VOID_TOK = -3,  // "void"
  FLOAT_TOK = -4, // "float"
  BOOL_TOK = -5,  // "bool"

  // keywords
  EXTERN = -6,  // "extern"
  IF = -7,      // "if"
  ELSE = -8,    // "else"
  WHILE = -9,   // "while"
  RETURN = -10, // "return"
  // TRUE   = -12,     // "true"
  // FALSE   = -13,     // "false"

  // literals
  INT_LIT = -14,   // [0-9]+
  FLOAT_LIT = -15, // [0-9]+.[0-9]+
  BOOL_LIT = -16,  // "true" or "false" key words

  // logical operators
  AND = -17, // "&&"
  OR = -18,  // "||"

  // operators
  PLUS = int('+'),    // addition or unary plus
  MINUS = int('-'),   // substraction or unary negative
  ASTERIX = int('*'), // multiplication
  DIV = int('/'),     // division
  MOD = int('%'),     // modular
  NOT = int('!'),     // unary negation

  // comparison operators
  EQ = -19,      // equal
  NE = -20,      // not equal
  LE = -21,      // less than or equal to
  LT = int('<'), // less than
  GE = -23,      // greater than or equal to
  GT = int('>'), // greater than

  // special tokens
  EOF_TOK = 0, // signal end of file

  // invalid
  INVALID = -100 // signal invalid token
};

// TOKEN struct is used to keep track of information about a token
struct TOKEN {
  int type = -100;
  std::string lexeme;
  int lineNo;
  int columnNo;
};

static std::string IdentifierStr; // Filled in if IDENT
static int IntVal;                // Filled in if INT_LIT
static bool BoolVal;              // Filled in if BOOL_LIT
static float FloatVal;            // Filled in if FLOAT_LIT
static std::string StringVal;     // Filled in if String Literal
static int lineNo, columnNo;

static TOKEN returnTok(std::string lexVal, int tok_type) {
  TOKEN return_tok;
  return_tok.lexeme = lexVal;
  return_tok.type = tok_type;
  return_tok.lineNo = lineNo;
  return_tok.columnNo = columnNo - lexVal.length() - 1;
  return return_tok;
}

// Read file line by line -- or look for \n and if found add 1 to line number
// and reset column number to 0
/// gettok - Return the next token from standard input.
static TOKEN gettok() {

  static int LastChar = ' ';
  static int NextChar = ' ';

  // Skip any whitespace.
  while (isspace(LastChar)) {
    if (LastChar == '\n' || LastChar == '\r') {
      lineNo++;
      columnNo = 1;
    }
    LastChar = getc(pFile);
    columnNo++;
  }

  if (isalpha(LastChar) ||
      (LastChar == '_')) { // identifier: [a-zA-Z_][a-zA-Z_0-9]*
    IdentifierStr = LastChar;
    columnNo++;

    while (isalnum((LastChar = getc(pFile))) || (LastChar == '_')) {
      IdentifierStr += LastChar;
      columnNo++;
    }

    if (IdentifierStr == "int")
      return returnTok("int", INT_TOK);
    if (IdentifierStr == "bool")
      return returnTok("bool", BOOL_TOK);
    if (IdentifierStr == "float")
      return returnTok("float", FLOAT_TOK);
    if (IdentifierStr == "void")
      return returnTok("void", VOID_TOK);
    if (IdentifierStr == "bool")
      return returnTok("bool", BOOL_TOK);
    if (IdentifierStr == "extern")
      return returnTok("extern", EXTERN);
    if (IdentifierStr == "if")
      return returnTok("if", IF);
    if (IdentifierStr == "else")
      return returnTok("else", ELSE);
    if (IdentifierStr == "while")
      return returnTok("while", WHILE);
    if (IdentifierStr == "return")
      return returnTok("return", RETURN);
    if (IdentifierStr == "true") {
      BoolVal = true;
      return returnTok("true", BOOL_LIT);
    }
    if (IdentifierStr == "false") {
      BoolVal = false;
      return returnTok("false", BOOL_LIT);
    }

    return returnTok(IdentifierStr.c_str(), IDENT);
  }

  if (LastChar == '=') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // EQ: ==
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("==", EQ);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("=", ASSIGN);
    }
  }

  if (LastChar == '{') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("{", LBRA);
  }
  if (LastChar == '}') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("}", RBRA);
  }
  if (LastChar == '(') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("(", LPAR);
  }
  if (LastChar == ')') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(")", RPAR);
  }
  if (LastChar == ';') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(";", SC);
  }
  if (LastChar == ',') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(",", COMMA);
  }

  if (isdigit(LastChar) || LastChar == '.') { // Number: [0-9]+.
    std::string NumStr;

    if (LastChar == '.') { // Floatingpoint Number: .[0-9]+
      do {
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      FloatVal = strtof(NumStr.c_str(), nullptr);
      return returnTok(NumStr, FLOAT_LIT);
    } else {
      do { // Start of Number: [0-9]+
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      if (LastChar == '.') { // Floatingpoint Number: [0-9]+.[0-9]+)
        do {
          NumStr += LastChar;
          LastChar = getc(pFile);
          columnNo++;
        } while (isdigit(LastChar));

        FloatVal = strtof(NumStr.c_str(), nullptr);
        return returnTok(NumStr, FLOAT_LIT);
      } else { // Integer : [0-9]+
        IntVal = strtod(NumStr.c_str(), nullptr);
        return returnTok(NumStr, INT_LIT);
      }
    }
  }

  if (LastChar == '&') {
    NextChar = getc(pFile);
    if (NextChar == '&') { // AND: &&
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("&&", AND);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("&", int('&'));
    }
  }

  if (LastChar == '|') {
    NextChar = getc(pFile);
    if (NextChar == '|') { // OR: ||
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("||", OR);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("|", int('|'));
    }
  }

  if (LastChar == '!') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // NE: !=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("!=", NE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("!", NOT);
      ;
    }
  }

  if (LastChar == '<') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // LE: <=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("<=", LE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("<", LT);
    }
  }

  if (LastChar == '>') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // GE: >=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok(">=", GE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok(">", GT);
    }
  }

  if (LastChar == '/') { // could be division or could be the start of a comment
    LastChar = getc(pFile);
    columnNo++;
    if (LastChar == '/') { // definitely a comment
      do {
        LastChar = getc(pFile);
        columnNo++;
      } while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

      if (LastChar != EOF)
        return gettok();
    } else
      return returnTok("/", DIV);
  }

  // Check for end of file.  Don't eat the EOF.
  if (LastChar == EOF) {
    columnNo++;
    return returnTok("0", EOF_TOK);
  }

  // Otherwise, just return the character as its ascii value.
  int ThisChar = LastChar;
  std::string s(1, ThisChar);
  LastChar = getc(pFile);
  columnNo++;
  return returnTok(s, int(ThisChar));
}

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static TOKEN CurTok;
static std::deque<TOKEN> tok_buffer;

static TOKEN getNextToken() {

  if (tok_buffer.size() == 0)
    tok_buffer.push_back(gettok());

  TOKEN temp = tok_buffer.front();
  tok_buffer.pop_front();

  return CurTok = temp;
}

static void putBackToken(TOKEN tok) { tok_buffer.push_front(tok); }

//===----------------------------------------------------------------------===//
// AST nodes
//===----------------------------------------------------------------------===//

/// ASTnode - Base class for all AST nodes.
class ASTnode {
public:
  virtual ~ASTnode() {}
  // Value *codegen() = 0;
  // std::string to_string() const {};
};

/// IntASTnode - Class for integer literals like 1, 2, 10,
class IntASTnode : public ASTnode {
  int Val;
  TOKEN Tok;
  std::string Name;

public:
  IntASTnode(TOKEN tok, int val) : Val(val), Tok(tok) {}
  // virtual Value *codegen() override;
  // virtual std::string to_string() const override {
  // return a sting representation of this AST node
  //};
};

class VarDeclASTnode : public ASTnode {
  TOKEN_TYPE Type; // may not be void
  std::string Value; // Identifier
  TOKEN Tok;

public:
  VarDeclASTnode(TOKEN tok, TOKEN_TYPE type, std::string value) : Tok(tok), Type(type), Value(value) {}
  // virtual Value *codegen() override;
};

class ParamASTnode : public ASTnode {
  TOKEN_TYPE Type; // may not be void
  std::string Value; // Identifier
  TOKEN Tok;

public:
  ParamASTnode(TOKEN tok, TOKEN_TYPE type, std::string value) : Tok(tok), Type(type), Value(value) {}
  // virtual Value *codegen() override;
};

class ParamsASTnode : public ASTnode {
  bool Is_Void;
  std::vector<std::unique_ptr<ParamASTnode>> Param_List;
  TOKEN Tok;

public:
  ParamsASTnode(TOKEN tok, bool is_void, std::vector<std::unique_ptr<ParamASTnode>> param_list) : Tok(tok), Is_Void(is_void), Param_List(std::move(param_list)) {}
  // virtual Value *codegen() override;
};

class ExternASTnode : public ASTnode {
  TOKEN_TYPE Type; // can be void
  std::string Identifier;
  std::unique_ptr<ParamsASTnode> Params;
  TOKEN Tok;

public:
  ExternASTnode(TOKEN tok, TOKEN_TYPE type, std::string identifier, std::unique_ptr<ParamsASTnode> params) : Tok(tok), Type(type), Identifier(identifier), Params(std::move(params)) {}
  // virtual Value *codegen() override;
};

class ExprASTnode;

class ArgListASTnode : public ASTnode {
  std::vector<std::unique_ptr<ExprASTnode>> Args_Expr_List;
  TOKEN Tok;
public:
  ArgListASTnode(TOKEN tok, std::vector<std::unique_ptr<ExprASTnode>> args_expr_list): Tok(tok), Args_Expr_List(std::move(args_expr_list)) {}
};


// base class for element AST nodes (priority 1 [highest] subexpressions)
class ElementASTnode : public ASTnode {

public:
  virtual ~ElementASTnode() {}
};

class PrefixOpElementASTnode : public ElementASTnode {
  TOKEN_TYPE Op; // may be - or !
  std::unique_ptr<ElementASTnode> Value_Element;
  TOKEN Tok;
public:
  PrefixOpElementASTnode(TOKEN tok, TOKEN_TYPE op, std::unique_ptr<ElementASTnode> value_element): Tok(tok), Op(op), Value_Element(std::move(value_element)) {}
};

class ParanthesisElementASTnode : public ElementASTnode {
  std::unique_ptr<ExprASTnode> Inner_Expr;
  TOKEN Tok;
public:
  ParanthesisElementASTnode(TOKEN tok, std::unique_ptr<ExprASTnode> inner_expr) : Tok(tok), Inner_Expr(std::move(inner_expr)) {}
};

class IdentElementASTnode : public ElementASTnode {
  std::string Value;
  TOKEN Tok;
public:
  IdentElementASTnode(TOKEN tok, std::string value) : Tok(tok), Value(value) {}
};

class IntElementASTnode : public ElementASTnode {
  int Value;
  TOKEN Tok;
public:
  IntElementASTnode(TOKEN tok, int value) : Tok(tok), Value(value) {}
};

class FloatElementASTnode: public ElementASTnode {
  float Value;
  TOKEN Tok;
public:
  FloatElementASTnode(TOKEN tok, float value) : Tok(tok), Value(value) {}
};

class BoolElementASTnode : public ElementASTnode {
  bool Value;
  TOKEN Tok;
public:
  BoolElementASTnode(TOKEN tok, bool value) : Tok(tok), Value(value) {}
};

class FunctionCallElementASTnode : public ElementASTnode {
  std::string Function_Name_Identifier;
  std::unique_ptr<ArgListASTnode> Args;
  TOKEN Tok;
public:
  FunctionCallElementASTnode(TOKEN tok, std::string function_name_identifier, std::unique_ptr<ArgListASTnode> args) : Tok(tok), Function_Name_Identifier(function_name_identifier), Args(std::move(args)) {}
};

// priority 2 subexpressions (*, /, %)
class FactorASTnode : public ASTnode {
  std::vector<std::unique_ptr<ElementASTnode>> Elements; // from left to right. non-empty
  std::vector<TOKEN_TYPE> Operators; // between each element in Elements. may be *, / or %. may be empty.
  TOKEN Tok;
public:
  FactorASTnode(TOKEN tok, std::vector<std::unique_ptr<ElementASTnode>> elements, std::vector<TOKEN_TYPE> operators) : Tok(tok), Elements(std::move(elements)), Operators(std::move(operators)) {}
};

// priority 3 subexpressions (+, -)
class SubexprASTnode : public ASTnode {
  std::vector<std::unique_ptr<FactorASTnode>> Factors; // from left to right. non-empty
  std::vector<TOKEN_TYPE> Operators; // between each factor in Factors. may be + or -. may be empty.
  TOKEN Tok;
public:
  SubexprASTnode(TOKEN tok, std::vector<std::unique_ptr<FactorASTnode>> factors, std::vector<TOKEN_TYPE> operators) : Tok(tok), Factors(std::move(factors)), Operators(std::move(operators)) {}
};

// priority 4 subexpressions (relations <=, <, >=, >)
class RelASTnode : public ASTnode {
  std::vector<std::unique_ptr<SubexprASTnode>> Subexprs; // from left to right. non-empty
  std::vector<TOKEN_TYPE> Operators; // between each subexpr in Subexprs. may be <=, <, > or >=. may be empty.
  TOKEN Tok;
public:
  RelASTnode(TOKEN tok, std::vector<std::unique_ptr<SubexprASTnode>> subexprs, std::vector<TOKEN_TYPE> operators) : Tok(tok), Subexprs(std::move(subexprs)), Operators(std::move(operators)) {}
};

// priority 5 subexpressions (equivalence ==)
class EquivASTnode : public ASTnode {
  std::vector<std::unique_ptr<RelASTnode>> Rels; // from left to right. non-empty
  std::vector<TOKEN_TYPE> Operators; // between each rel in Rels. may be == or !=. may be empty.
  TOKEN Tok;
public:
  EquivASTnode(TOKEN tok, std::vector<std::unique_ptr<RelASTnode>> rels, std::vector<TOKEN_TYPE> operators) : Tok(tok), Rels(std::move(rels)), Operators(std::move(operators)) {}
};

// priority 6 subexpressions (&&)
class TermASTnode : public ASTnode {
  std::vector<std::unique_ptr<EquivASTnode>> Equivs; // from left to right. non-empty
  TOKEN Tok;
  // we void the Operators vector because we know the only operator is && and it is applied between each equiv in Equivs.
public:
  TermASTnode(TOKEN tok, std::vector<std::unique_ptr<EquivASTnode>> equivs) : Tok(tok), Equivs(std::move(equivs)) {}
};

// priority 7 subexpressions (||)
class RValASTnode : public ASTnode {
  std::vector<std::unique_ptr<TermASTnode>> Terms; // from left to right. non-empty
  TOKEN Tok;
  // we void the Operators vector because we know the only operator is || and it is applied between each term in Terms.
public:
  RValASTnode(TOKEN tok, std::vector<std::unique_ptr<TermASTnode>> terms) : Tok(tok), Terms(std::move(terms)) {}
};

// base class for priority 8 [least] subexpressions
class ExprASTnode : public ASTnode {

public:
 virtual ~ExprASTnode() {}
};

// priority 8 [least] assignment subexpression
class AssignExprASTnode : public ExprASTnode {
  std::string Var_Name_Identifier;
  std::unique_ptr<ExprASTnode> Value_Expr;
  TOKEN Tok;

public:
  AssignExprASTnode(TOKEN tok, std::string var_name_identifier, std::unique_ptr<ExprASTnode> value_expr) : Tok(tok), Var_Name_Identifier(std::move(var_name_identifier)), Value_Expr(std::move(value_expr)) {}
};

// priority 8 [least] rval delegation subexpression
class RValExprASTnode : public ExprASTnode {
  std::unique_ptr<RValASTnode> RVal;
  TOKEN Tok;

public:
  RValExprASTnode(TOKEN tok, std::unique_ptr<RValASTnode> rval) : Tok(tok), RVal(std::move(rval)) {}
};

// Base class for stmt
class StmtASTnode : public ASTnode {

public:
  virtual ~StmtASTnode() {}
};

class ExprStmtASTnode : public StmtASTnode {
  std::unique_ptr<ExprASTnode> Expr; // may be null
  TOKEN Tok;

public:
  ExprStmtASTnode(TOKEN tok, std::unique_ptr<ExprASTnode> expr) : Tok(tok), Expr(std::move(expr)) {}
};

class ReturnStmtASTnode : public StmtASTnode {
  std::unique_ptr<ExprStmtASTnode> Return_Expr_Stmt;
  TOKEN Tok;

public:
  ReturnStmtASTnode(TOKEN tok, std::unique_ptr<ExprStmtASTnode> return_expr_stmt): Tok(tok), Return_Expr_Stmt(std::move(return_expr_stmt)) {}
};


class BlockASTnode; // forward declaring BlockASTnode due to the cyclic dependency between BlockASTnode and IfStmtASTnode

class IfStmtASTnode : public StmtASTnode {
  std::unique_ptr<ExprASTnode> Condition_Expr;
  std::unique_ptr<BlockASTnode> If_Body;
  std::unique_ptr<BlockASTnode> Else_Body; // may be null for no else
  TOKEN Tok;

public:
  IfStmtASTnode(TOKEN tok, std::unique_ptr<ExprASTnode> condition_expr, std::unique_ptr<BlockASTnode> if_body, std::unique_ptr<BlockASTnode> else_body): Tok(tok), Condition_Expr(std::move(condition_expr)), If_Body(std::move(if_body)), Else_Body(std::move(else_body)) {}
};

class WhileStmtASTnode : public StmtASTnode {
  std::unique_ptr<ExprASTnode> Condition_Expr;
  std::unique_ptr<StmtASTnode> Body_Stmt;
  TOKEN Tok;

public:
  WhileStmtASTnode(TOKEN tok, std::unique_ptr<ExprASTnode> condition_expr, std::unique_ptr<StmtASTnode> body_stmt): Tok(tok), Condition_Expr(std::move(condition_expr)), Body_Stmt(std::move(body_stmt)) {}
};


class BlockASTnode : public StmtASTnode {
  std::vector<std::unique_ptr<VarDeclASTnode>> Local_Decls;
  std::vector<std::unique_ptr<StmtASTnode>> Stmts;
  TOKEN Tok;

public:
  BlockASTnode(TOKEN tok, std::vector<std::unique_ptr<VarDeclASTnode>> local_decls, std::vector<std::unique_ptr<StmtASTnode>> stmts) : Tok(tok), Local_Decls(std::move(local_decls)), Stmts(std::move(stmts)) {}
  // virtual Value *codegen() override;
};

// may contain void
class FunDeclASTnode : public ASTnode {
  TOKEN_TYPE Return_Type; // may be void
  std::string Name;
  std::unique_ptr<ParamsASTnode> Params;
  std::unique_ptr<BlockASTnode> Body; // Block
  TOKEN Tok;

public:
  FunDeclASTnode(TOKEN tok, TOKEN_TYPE return_type, std::string name, std::unique_ptr<ParamsASTnode> params, std::unique_ptr<BlockASTnode> body) : Tok(tok), Return_Type(return_type), Name(name), Params(std::move(params)), Body(std::move(body)) {}
  // virtual Value *codegen() override;
};

class DeclASTnode : public ASTnode {
  std::unique_ptr<VarDeclASTnode> Var_Decl;
  std::unique_ptr<FunDeclASTnode> Fun_Decl;
  bool Is_Var_Decl;
  TOKEN Tok;
public:
  DeclASTnode(TOKEN tok, std::unique_ptr<VarDeclASTnode> var_decl, std::unique_ptr<FunDeclASTnode> fun_decl, bool is_var_decl) : Tok(tok), Var_Decl(std::move(var_decl)), Fun_Decl(std::move(fun_decl)), Is_Var_Decl(is_var_decl) {}
  // virtual Value *codegen() override;
};

class ProgramASTnode : public ASTnode {
  std::vector<std::unique_ptr<ExternASTnode>> Extern_List;
  std::vector<std::unique_ptr<DeclASTnode>> Decl_List;
  TOKEN Tok;
public:
  ProgramASTnode(TOKEN tok, std::vector<std::unique_ptr<ExternASTnode>> extern_list, std::vector<std::unique_ptr<DeclASTnode>> decl_list) : Tok(tok), Extern_List(std::move(extern_list)), Decl_List(std::move(decl_list)) {}
  // virtual Value *codegen() override;
};

/* add other AST nodes as nessasary */

//===----------------------------------------------------------------------===//
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

/* Add function calls for each production */

static bool TokenContains(std::vector<TOKEN_TYPE> allowed_tokens, int token) 
{
  for (auto allowed_token : allowed_tokens) {
    if (allowed_token == token) return true;
  }
  return false;
}

// parses ("int" | "float" | "bool"), and if can_be_void, also (| "void")
static TOKEN_TYPE ParseType(bool can_be_void, std::string production_name) {
  std::vector<TOKEN_TYPE> legal_values_base = {INT_TOK, FLOAT_TOK, BOOL_TOK};
  if (!TokenContains(legal_values_base, CurTok.type) && (!can_be_void || CurTok.type != VOID_TOK)) {
    std::stringstream ss;
    ss << "Expected " << production_name << " to be one of 'int', 'float', 'bool'" << (can_be_void ? ", 'void'" : "") << ".";
    perror(ss.str().c_str());
    return INVALID;
  }
  // eat the type
  auto type = CurTok.type;
  getNextToken();
  return static_cast<TOKEN_TYPE>(type);
}

// param ::= var_type IDENT
static std::unique_ptr<ParamASTnode> ParseParam() {
  // parse the var_type
  auto type = ParseType(false, "var_type"); // cannot be void

  // eat the identifier which is the variable name
  if (CurTok.type != IDENT) {
    perror("Expected an identifier to follow the type of a var_decl.");
    return nullptr;
  }
  auto name = IdentifierStr;
  getNextToken();

  return std::make_unique<ParamASTnode>(CurTok, type, name);
}

/* params ::= param_list  
          |  "void" | epsilon 
  param_list ::= param param_list2
  param_list2 ::= "," param param_list | epsilon */
static std::unique_ptr<ParamsASTnode> ParseParams() {
  std::vector<TOKEN_TYPE> param_list_first = {INT_TOK, FLOAT_TOK, BOOL_TOK};
  if (TokenContains(param_list_first, CurTok.type)) {
    std::vector<std::unique_ptr<ParamASTnode>> param_list;
    // parse first param
    auto firstParam = ParseParam();
    param_list.push_back(std::move(firstParam));
    // parse the rest, which are separated by commas
    while (CurTok.type == COMMA) {
      // eat ','
      getNextToken();
      auto param = ParseParam();
      param_list.push_back(std::move(param));
    }
    return std::make_unique<ParamsASTnode>(CurTok, false, std::move(param_list));
  }
  if (CurTok.type == VOID_TOK) { // is just void
    // eat void
    getNextToken();
    return std::make_unique<ParamsASTnode>(CurTok, true, std::move(std::vector<std::unique_ptr<ParamASTnode>>()));
  }
  if (CurTok.type == RPAR) { // current token is in follow of params, thus do nothing but is still valid production
    return std::make_unique<ParamsASTnode>(CurTok, false, std::move(std::vector<std::unique_ptr<ParamASTnode>>()));
  }
  perror("Expected params to be either a list of param declarations, 'void', or empty, but is neither.");
  return nullptr;
}

// var_decl ::= var_type IDENT ";" 
static std::unique_ptr<VarDeclASTnode> ParseVarDecl() {
  // parse the var_type
  auto type = ParseType(false, "var_decl"); // cannot be void

  // eat the identifier which is the variable name
  if (CurTok.type != IDENT) {
    perror("Expected an identifier to follow the type of a var_decl.");
    return nullptr;
  }
  auto name = IdentifierStr;
  getNextToken();

  // eat the ';'
  if (CurTok.type != SC) {
    perror("Expected ';' to follow the variable name in a var_decl.");
    return nullptr;
  }
  getNextToken();

  return std::make_unique<VarDeclASTnode>(CurTok, type, name);
}

static std::unique_ptr<BlockASTnode> ParseBlock(); // forward declaring ParseBlock due to cyclic dependency between ParseFunDecl and ParseBlock

// fun_decl ::= type_spec IDENT "(" params ")" block
static std::unique_ptr<FunDeclASTnode> ParseFunDecl() {
  // parse type_spec
  auto return_type = ParseType(true, "type_spec"); // can be void

  // eat the identifier which is the function name
  if (CurTok.type != IDENT) {
    perror("Expected an identifier to follow the type of a fun_decl.");
    return nullptr;
  }
  auto name = IdentifierStr;
  getNextToken();

  // eat the '('
  if (CurTok.type != LPAR) {
    perror("Expected '(' to follow the function name in a fun_decl.");
    return nullptr;
  }
  getNextToken();

  auto params = ParseParams();

  // eat the ')'
  if (CurTok.type != RPAR) {
    perror("Expected ')' to follow params in a fun_decl.");
    return nullptr;
  }
  getNextToken();

  auto body = ParseBlock();

  return std::make_unique<FunDeclASTnode>(CurTok, return_type, name, std::move(params), std::move(body));
}

/* decl ::= var_decl 
        |  fun_decl */
static std::unique_ptr<DeclASTnode> ParseDecl() {
  auto first_token = CurTok;
  // need to look ahead 3 tokens here 
  auto second_token = getNextToken();
  auto third_token = getNextToken();
  // put tokens back in buffer
  putBackToken(third_token);
  putBackToken(second_token);
  CurTok = first_token;
  if (first_token.type == VOID_TOK || third_token.type == LPAR) {
    // is fun_decl
    auto fun_decl = ParseFunDecl();
    return std::make_unique<DeclASTnode>(CurTok, nullptr, std::move(fun_decl), false);
  }
  else if (third_token.type == SC) {
    // is var_decl
    auto var_decl = ParseVarDecl();
    return std::make_unique<DeclASTnode>(CurTok, std::move(var_decl), nullptr, true);
  }
  else {
    perror("Expected var_decl or fun_decl in decl.");
  }
  return nullptr;
}

/* decl_list ::= decl decl_list
             |  decl */
static std::vector<std::unique_ptr<DeclASTnode>> ParseDeclList() {
  std::vector<TOKEN_TYPE> decl_list_first = {INT_TOK, FLOAT_TOK, BOOL_TOK, VOID_TOK};
  std::vector<std::unique_ptr<DeclASTnode>> decl_list;
  if (!TokenContains(decl_list_first, CurTok.type)) {
    perror("Expected at least one declaration in decl_list.");
    return std::vector<std::unique_ptr<DeclASTnode>>();
  }
  do {
    auto decl = ParseDecl();
    if (decl) {
      decl_list.push_back(std::move(decl));
    }
  } while (TokenContains(decl_list_first, CurTok.type));
  return std::move(decl_list);
}

/* local_decls ::= var_decl local_decls
               |  epsilon */
static std::vector<std::unique_ptr<VarDeclASTnode>> ParseLocalDecls() {
  std::vector<std::unique_ptr<VarDeclASTnode>> var_decls;
  std::vector<TOKEN_TYPE> var_decl_first = {INT_TOK, FLOAT_TOK, BOOL_TOK};
  while (TokenContains(var_decl_first, CurTok.type)) {
    auto var_decl = ParseVarDecl();
    var_decls.push_back(std::move(var_decl));
  }
  return std::move(var_decls);
}

static std::vector<std::unique_ptr<StmtASTnode>> ParseStmtList(); // forward declaring ParseStmtList since there is a cyclic dependency between ParseBlock and ParseStmtList

// block ::= "{" local_decls stmt_list "}"
static std::unique_ptr<BlockASTnode> ParseBlock() {
  // eat '{'
  if (CurTok.type != LBRA) {
    errs() << "Expected block to begin with '{'\n" << "Line # " << lineNo << "\nCur tok: " << CurTok.lexeme; 
    return nullptr;
  }
  getNextToken();
  auto local_decls = ParseLocalDecls();
  auto stmts = ParseStmtList();
  return std::make_unique<BlockASTnode>(CurTok, std::move(local_decls), std::move(stmts));
}

static std::unique_ptr<RValASTnode> ParseRVal(); // forward declaring ParseRVal for ParseExpr

/* expr ::= IDENT "=" expr
        | rval */
static std::unique_ptr<ExprASTnode> ParseExpr() {
  std::vector<TOKEN_TYPE> expr_first = {IDENT, MINUS, NOT, LPAR, INT_LIT, FLOAT_LIT, BOOL_LIT};
  if (!TokenContains(expr_first, CurTok.type)) {
    errs() << "Expected expr to begin with one of identifier, unary -/!, (, or int/float/bool, but was none.\n" << "Line # " << lineNo << "\nCur tok: " << CurTok.lexeme;
    return nullptr;
  }
  bool isRVal = false;
  if (CurTok.type != IDENT) {
    isRVal = true;
  } 
  else {
    // since the first of both productions contains IDENT, must look at second look ahead symbol to determine production
    // since rval's second symbol can be '||' or its follow set, which does not contain '=', checking the second lookahead symbol as '=' uniquely determines whether it's the assignment or the rval production
    auto first_token = CurTok;
    // obtain the second look ahead token
    auto second_token = getNextToken();
    isRVal = second_token.type != ASSIGN;
    // put back second_token
    putBackToken(second_token);
    CurTok = first_token;
  }
  if (isRVal) {
    auto rval = ParseRVal();
    return std::make_unique<RValExprASTnode>(CurTok, std::move(rval));
  }
  // is assignment
  auto var_name_identifier = IdentifierStr;
  getNextToken();
  // we know this token is '=' because we already looked ahead. eat the '='.
  getNextToken();
  auto value_expr = ParseExpr();
  return std::make_unique<AssignExprASTnode>(CurTok, var_name_identifier, std::move(value_expr));
}

/* expr_stmt ::= expr ";" 
             |  ";" */
static std::unique_ptr<ExprStmtASTnode> ParseExprStmt() {
  std::vector<TOKEN_TYPE> expr_first = {IDENT, MINUS, NOT, LPAR, INT_LIT, FLOAT_LIT, BOOL_LIT};
  std::unique_ptr<ExprASTnode> expr = nullptr;
  if (TokenContains(expr_first, CurTok.type)) {
    // begins with an expr
    expr = ParseExpr();
  }
  // eat the ';'
  if (CurTok.type != SC) {
    errs() << "Expected ';' at the end of expr_stmt.\n" << "Line # " << lineNo << "\nCur tok: " << CurTok.lexeme; 
    return nullptr;
  }
  getNextToken();
  return std::make_unique<ExprStmtASTnode>(CurTok, std::move(expr)); // false for not a return stmt
}

// if_stmt ::= "if" "(" expr ")" block else_stmt
/* else_stmt  ::= "else" block
              |  epsilon */
static std::unique_ptr<IfStmtASTnode> ParseIfStmt() {
  // eat 'if'
  if (CurTok.type != IF) {
    perror("Expected if_stmt to begin with 'if'.");
    return nullptr;
  }
  getNextToken();
  // eat '('
  if (CurTok.type != LPAR) {
    perror("Expected '(' to follow 'if' in if_stmt.");
    return nullptr;
  }
  getNextToken();
  auto condition_expr = ParseExpr();
  // eat ')'
  if (CurTok.type != RPAR) {
    perror("Expected ')' to follow the if condition expression in if_stmt.");
    return nullptr;
  }
  getNextToken();
  auto if_body = ParseBlock();
  // parse else if exists
  std::unique_ptr<BlockASTnode> else_body = nullptr; 
  if (CurTok.type == ELSE) {
    // eat 'else'
    getNextToken();
    else_body = ParseBlock();
  }
  return std::make_unique<IfStmtASTnode>(CurTok, std::move(condition_expr), std::move(if_body), std::move(else_body));
}

static std::unique_ptr<StmtASTnode> ParseStmt(); // forward declaring ParseStmt due to cyclic dependency between ParseWhileStmt and ParseStmt

// while_stmt ::= "while" "(" expr ")" stmt 
static std::unique_ptr<WhileStmtASTnode> ParseWhileStmt() {
  // eat 'while'
  if (CurTok.type != WHILE) {
    perror("Expected while_stmt to begin with 'while'.");
    return nullptr;
  }
  getNextToken();
  // eat '('
  if (CurTok.type != LPAR) {
    perror("Expected '(' to follow 'while' in while_stmt.");
    return nullptr;
  }
  getNextToken();
  auto condition_expr = ParseExpr();
  // eat ')'
  if (CurTok.type != RPAR) {
    perror("Expected ')' to follow the while condition expression in while_stmt.");
    return nullptr;
  }
  getNextToken();
  auto body_stmt = ParseStmt();
  return std::make_unique<WhileStmtASTnode>(CurTok, std::move(condition_expr), std::move(body_stmt));
}

// return_stmt ::= "return" expr_stmt
static std::unique_ptr<ReturnStmtASTnode> ParseReturnStmt() {
  // eat 'return'
  if (CurTok.type != RETURN) {
    perror("Expected return_stmt to begin with 'return'.");
    return nullptr;
  }
  getNextToken();
  auto return_expr_stmt = ParseExprStmt();
  return std::make_unique<ReturnStmtASTnode>(CurTok, std::move(return_expr_stmt));
}

/* stmt ::= expr_stmt 
        |  block 
        |  if_stmt 
        |  while_stmt 
        |  return_stmt */
static std::unique_ptr<StmtASTnode> ParseStmt() {
  std::vector<TOKEN_TYPE> expr_stmt_first = {SC, IDENT, MINUS, NOT, LPAR, IDENT, INT_TOK, FLOAT_TOK, BOOL_TOK};
  if (TokenContains(expr_stmt_first, CurTok.type)) { 
    // is expr_stmt
    auto expr_stmt = ParseExprStmt();
    return std::move(expr_stmt);
  }
  else if (CurTok.type == LBRA) { 
    // is block
    auto block = ParseBlock();
    return std::move(block);
  }
  else if (CurTok.type == IF) { 
    // is if_stmt
    auto if_stmt = ParseIfStmt();
    return std::move(if_stmt);
  }
  else if (CurTok.type == WHILE) {
    // is while_stmt
    auto while_stmt = ParseWhileStmt();
    return std::move(while_stmt);
  }
  else if (CurTok.type == RETURN) {
    // is return_stmt
    auto return_stmt = ParseReturnStmt();
    return std::move(return_stmt);
  }
  perror("Expected stmt to be one of an expr_stmt, block, if_stmt, while_stmt or return_stmt, but was none.");
  return nullptr;
}

/* stmt_list ::= stmt stmt_list
             |  epsilon */
static std::vector<std::unique_ptr<StmtASTnode>> ParseStmtList() {
  std::vector<std::unique_ptr<StmtASTnode>> stmt_list;
  std::vector<TOKEN_TYPE> stmt_first = {SC, IDENT, MINUS, NOT, LPAR, INT_TOK, FLOAT_TOK, BOOL_TOK, LBRA, IF, WHILE, RETURN};
  while (TokenContains(stmt_first, CurTok.type)) {
    auto stmt = ParseStmt();
    stmt_list.push_back(std::move(stmt));
  }
  return std::move(stmt_list);
}

// extern ::= "extern" type_spec IDENT "(" params ")" ";"
static std::unique_ptr<ExternASTnode> ParseExtern() {
  if (CurTok.type != EXTERN) {
    perror("Expected extern to begin with 'extern'.");
    return nullptr;
  }
  // eat "extern"
  getNextToken();
  // parse type_spec
  auto type_spec = ParseType(true, "type_spec"); // can be void
  // identifier
  if (CurTok.type != IDENT) {
    perror("Expected IDENT to follow type_spec in extern.");
    return nullptr;
  }
  auto identifier = IdentifierStr;
  // eat identifier
  getNextToken();
  // '('
  if (CurTok.type != LPAR) {
    perror("Expected '(' to follow IDENT in extern.");
    return nullptr;
  }
  // eat '('
  getNextToken();
  // params
  auto params = ParseParams();
  if (!params) {
    perror("Expected params to follow '(' in extern.");
    return nullptr;
  }
  // ')'
  if (CurTok.type != RPAR) {
    perror("Expected ')' to follow params in extern.");
    return nullptr;
  }
  // eat ')'
  getNextToken();
  // ';'
  if (CurTok.type != SC) {
    perror("Expected ';' to follow ')' in extern.");
    return nullptr;
  }
  // eat ';'
  getNextToken();
  return std::make_unique<ExternASTnode>(CurTok, std::move(type_spec), identifier, std::move(params));
}

/* extern_list ::= extern extern_list
               |  extern */
static std::vector<std::unique_ptr<ExternASTnode>> ParseExternList() {
  std::vector<std::unique_ptr<ExternASTnode>> extern_list;
  auto first_extern = ParseExtern();
  if (!first_extern) {
    perror("Expected at least one extern in extern_list.");
    return std::vector<std::unique_ptr<ExternASTnode>>();
  }
  while (CurTok.type == EXTERN) {
    auto externn = ParseExtern();
    extern_list.push_back(std::move(externn));
  } 
  return std::move(extern_list);
}

/* args ::= arg_list 
        |  epsilon
  arg_list ::= expr arg_list2
  arg_list2 ::= "," expr arg_list2 | epsilon */
static std::unique_ptr<ArgListASTnode> ParseArgs() {
  std::vector<TOKEN_TYPE> expr_first = {IDENT, MINUS, NOT, LPAR, INT_LIT, FLOAT_LIT, BOOL_LIT};
  std::vector<std::unique_ptr<ExprASTnode>> args_expr_list;
  if (TokenContains(expr_first, CurTok.type)) {
    auto expr = ParseExpr();
    args_expr_list.push_back(std::move(expr));
  }
  // the rest are separated by ','
  while (CurTok.type == COMMA) {
    // eat the ','
    getNextToken();
    auto expr = ParseExpr();
    args_expr_list.push_back(std::move(expr));
  }
  return std::make_unique<ArgListASTnode>(CurTok, std::move(args_expr_list));
}

// element ::= "-" element | "!" element | "(" expr ")" | IDENT | IDENT "(" args ")" | INT_LIT | FLOAT_LIT | BOOL_LIT
static std::unique_ptr<ElementASTnode> ParseElement() {
  if (CurTok.type == MINUS || CurTok.type == NOT) {
    // is PrefixOp with unary - or !
    auto op = static_cast<TOKEN_TYPE>(CurTok.type);
    // eat the unary operator
    getNextToken();
    auto value_element = ParseElement();
    return std::make_unique<PrefixOpElementASTnode>(CurTok, op, std::move(value_element));
  }
  else if (CurTok.type == LPAR) {
    // is Parenthesis
    // eat the '('
    getNextToken();
    auto inner_expr = ParseExpr();
    // eat the ')'
    if (CurTok.type != RPAR) {
      perror("Expected ')' to follow the expr inside parenthesis element.");
      return nullptr;
    }
    getNextToken();
    return std::make_unique<ParanthesisElementASTnode>(CurTok, std::move(inner_expr));
  }
  else if (CurTok.type == IDENT) {
    // is either an Identifier of a FunctionCall, lookahead another to determine
    auto ident_value = IdentifierStr;
    // eat the identifier
    getNextToken();
    // note that '(' is not in the follow set of element, thus checking '(' uniquely narrows down to a function call
    if (CurTok.type == LPAR) {
      // is a function call
      // eat the '('
      getNextToken();
      auto args = ParseArgs();
      // eat the ')'
      if (CurTok.type != RPAR) {
        perror("Expected ')' after args in a function call.");
        return nullptr;
      }
      getNextToken();
      return std::make_unique<FunctionCallElementASTnode>(CurTok, ident_value, std::move(args));
    }
    else {
      // is just an identifier
      return std::make_unique<IdentElementASTnode>(CurTok, ident_value);
    }
  }
  else if (CurTok.type == INT_LIT) {
    // is int literal
    auto int_val = IntVal;
    getNextToken();
    return std::make_unique<IntElementASTnode>(CurTok, int_val);
  }
  else if (CurTok.type == FLOAT_LIT) {
    // is float literal
    auto float_val = FloatVal;
    getNextToken();
    return std::make_unique<FloatElementASTnode>(CurTok, float_val);
  }
  else if (CurTok.type == BOOL_LIT) {
    // is bool literal
    auto bool_val = BoolVal;
    getNextToken();
    return std::make_unique<BoolElementASTnode>(CurTok, bool_val);
  }
  printf("Expected element to be one of unary +/-, identifier, function call, int/float/bool literal, but was none.");
  return nullptr;
}

/* factor ::= element factor2
  factor2 ::= "*" element factor2 | "/" element factor2 | "%" element factor2 | epsilon */
static std::unique_ptr<FactorASTnode> ParseFactor() {
  std::vector<std::unique_ptr<ElementASTnode>> elements;
  std::vector<TOKEN_TYPE> operators;
  std::vector<TOKEN_TYPE> element_first = {MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT};
  // parse first element
  if (!TokenContains(element_first, CurTok.type)) {
    perror("Expected factor to begin with at least one element.");
    return nullptr;
  }
  auto first_element = ParseElement();
  elements.push_back(std::move(first_element));
  // parse the rest of the elements separated by operators
  std::vector<TOKEN_TYPE> factor2_first = {ASTERIX, DIV, MOD};
  while (TokenContains(factor2_first, CurTok.type)) {
    auto op = CurTok.type;
    operators.push_back(static_cast<TOKEN_TYPE>(op));
    getNextToken();
    auto rhs_element = ParseElement();
    elements.push_back(std::move(rhs_element));
  }
  return std::make_unique<FactorASTnode>(CurTok, std::move(elements), std::move(operators));
}

/* subexpr ::= factor subexpr2
  subexpr2 ::= "+" factor subexpr2 | "-" factor subexpr2 | epsilon */
static std::unique_ptr<SubexprASTnode> ParseSubexpr() {
  std::vector<std::unique_ptr<FactorASTnode>> factors;
  std::vector<TOKEN_TYPE> operators;
  std::vector<TOKEN_TYPE> factor_first = {MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT};
  // parse first element
  if (!TokenContains(factor_first, CurTok.type)) {
    perror("Expected subexpr to begin with at least one factor.");
    return nullptr;
  }
  auto first_factor = ParseFactor();
  factors.push_back(std::move(first_factor));
  // parse the rest of the factors separated by operators
  std::vector<TOKEN_TYPE> subexpr2_first = {PLUS, MINUS};
  while (TokenContains(subexpr2_first, CurTok.type)) {
    auto op = CurTok.type;
    operators.push_back(static_cast<TOKEN_TYPE>(op));
    getNextToken();
    auto rhs_factor = ParseFactor();
    factors.push_back(std::move(rhs_factor));
  }
  return std::make_unique<SubexprASTnode>(CurTok, std::move(factors), std::move(operators));
}

/* rel ::= subexpr rel2
  rel2 ::= "<=" subexpr rel2 | "<" subexpr rel2 | ">=" subexpr rel2 | ">" subexpr rel2 | epsilon */
static std::unique_ptr<RelASTnode> ParseRel() {
  std::vector<std::unique_ptr<SubexprASTnode>> subexprs;
  std::vector<TOKEN_TYPE> operators;
  std::vector<TOKEN_TYPE> subexpr_first = {MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT};
  // parse first element
  if (!TokenContains(subexpr_first, CurTok.type)) {
    perror("Expected rel to begin with at least one subexpr.");
    return nullptr;
  }
  auto first_subexpr = ParseSubexpr();
  subexprs.push_back(std::move(first_subexpr));
  // parse the rest of the subexprs separated by operators
  std::vector<TOKEN_TYPE> rel2_first = {GT, GE, LT, LE};
  while (TokenContains(rel2_first, CurTok.type)) {
    auto op = CurTok.type;
    operators.push_back(static_cast<TOKEN_TYPE>(op));
    getNextToken();
    auto rhs_subexpr = ParseSubexpr();
    subexprs.push_back(std::move(rhs_subexpr));
  }
  return std::make_unique<RelASTnode>(CurTok, std::move(subexprs), std::move(operators));
}

/* equiv ::= rel equiv2
  equiv2 ::= "==" rel equiv2 | "!=" rel equiv2 | epsilon */
static std::unique_ptr<EquivASTnode> ParseEquiv() {
  std::vector<std::unique_ptr<RelASTnode>> rels;
  std::vector<TOKEN_TYPE> operators;
  std::vector<TOKEN_TYPE> rel_first = {MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT};
  // parse first element
  if (!TokenContains(rel_first, CurTok.type)) {
    perror("Expected equiv to begin with at least one rel.");
    return nullptr;
  }
  auto first_rel = ParseRel();
  rels.push_back(std::move(first_rel));
  // parse the rest of the rels separated by operators
  std::vector<TOKEN_TYPE> equiv2_first = {EQ, NE};
  while (TokenContains(equiv2_first, CurTok.type)) {
    auto op = CurTok.type;
    operators.push_back(static_cast<TOKEN_TYPE>(op));
    getNextToken();
    auto rhs_rel = ParseRel();
    rels.push_back(std::move(rhs_rel));
  }
  return std::make_unique<EquivASTnode>(CurTok, std::move(rels), std::move(operators));
}

/* term ::= equiv term2
  term2 ::= "&&" equiv term2 | epsilon */
static std::unique_ptr<TermASTnode> ParseTerm() {
  std::vector<std::unique_ptr<EquivASTnode>> equivs;
  std::vector<TOKEN_TYPE> equiv_first = {MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT};
  // parse first element
  if (!TokenContains(equiv_first, CurTok.type)) {
    perror("Expected term to begin with at least one equiv.");
    return nullptr;
  }
  auto first_equiv = ParseEquiv();
  equivs.push_back(std::move(first_equiv));
  // parse the rest of the equivs separated by operators
  while (CurTok.type == AND) {
    getNextToken();
    auto rhs_equiv = ParseEquiv();
    equivs.push_back(std::move(rhs_equiv));
  }
  return std::make_unique<TermASTnode>(CurTok, std::move(equivs));
}

/* rval ::= term rval2
  rval2 ::= "||" term rval2 | epsilon */
static std::unique_ptr<RValASTnode> ParseRVal() {
  std::vector<std::unique_ptr<TermASTnode>> terms;
  std::vector<TOKEN_TYPE> term_first = {MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT};
  // parse first element
  if (!TokenContains(term_first, CurTok.type)) {
    perror("Expected rval to begin with at least one term.");
    return nullptr;
  }
  auto first_term = ParseTerm();
  terms.push_back(std::move(first_term));
  // parse the rest of the equivs separated by operators
  while (CurTok.type == OR) {
    getNextToken();
    auto rhs_term = ParseTerm();
    terms.push_back(std::move(rhs_term));
  }
  return std::make_unique<RValASTnode>(CurTok, std::move(terms));
}

// program ::= extern_list decl_list | decl_list
static std::unique_ptr<ASTnode> ParseProgram() {
  std::vector<TOKEN_TYPE> decl_list_first = {INT_TOK, FLOAT_TOK, BOOL_TOK, VOID_TOK};
  std::vector<std::unique_ptr<ExternASTnode>> extern_list = CurTok.type == EXTERN ? ParseExternList() : std::vector<std::unique_ptr<ExternASTnode>>();
  if (TokenContains(decl_list_first, CurTok.type)) {
    auto decl_list = ParseDeclList();
    return std::make_unique<ProgramASTnode>(CurTok, std::move(extern_list), std::move(decl_list));
  }
  else {
    perror("Expected at least one declaration in program.");
  }
  return nullptr;
}

// program ::= extern_list decl_list | decl_list
static void parser() {
  ParseProgram();
}






//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;

//===----------------------------------------------------------------------===//
// AST Printer
//===----------------------------------------------------------------------===//

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
                                     const ASTnode &ast) {
  // os << ast.to_string();
  os << "use above when doing";
  return os;
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main(int argc, char **argv) {
  if (argc == 2) {
    pFile = fopen(argv[1], "r");
    if (pFile == NULL)
      perror("Error opening file");
  } else {
    std::cout << "Usage: ./code InputFile\n";
    return 1;
  }

  // initialize line number and column numbers to zero
  lineNo = 1;
  columnNo = 1;

  // get the first token
  auto first_token = getNextToken();
  // while (CurTok.type != EOF_TOK) {
  //   fprintf(stderr, "Token: %s with type %d\n", CurTok.lexeme.c_str(),
  //           CurTok.type);
  //   getNextToken();
  // }
  // fprintf(stderr, "Lexer Finished\n");

  // Make the module, which holds all the code.
  TheModule = std::make_unique<Module>("mini-c", TheContext);

  // Run the parser now.
  parser();
  fprintf(stderr, "Parsing Finished\n");

  //********************* Start printing final IR **************************
  // Print out all of the generated code into a file called output.ll
  auto Filename = "output.ll";
  std::error_code EC;
  raw_fd_ostream dest(Filename, EC, sys::fs::F_None);

  if (EC) {
    errs() << "Could not open file: " << EC.message();
    return 1;
  }
  // TheModule->print(errs(), nullptr); // print IR to terminal
  TheModule->print(dest, nullptr);
  //********************* End printing final IR ****************************

  fclose(pFile); // close the file that contains the code that was parsed
  return 0;
}
