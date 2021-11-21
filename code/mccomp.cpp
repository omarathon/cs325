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
// Lexer Helper Functions
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
// Code Generation Variables and Helper Functions
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;

static std::map<std::string, AllocaInst*> NamedValues; // local var table(s)
static std::map<std::string, Value *> GlobalNamedValues; //global var table
static std::map<std::string, Function *> Functions;

/// Create an alloca instruction in the entry block of the function
static AllocaInst *CreateEntryBlockAlloca(Function *TheFunction,
                                          const std::string &VarName,
                                          Type *Type) {
  IRBuilder<> tempBuilder(&TheFunction->getEntryBlock(), TheFunction->getEntryBlock().begin());
  return tempBuilder.CreateAlloca(Type, 0, VarName.c_str());
}

// Get the type of the given token and convert it to an llvm::Type
static Type *GetTokenLLVMType(TOKEN tok) {
  switch (tok.type) {
    case INT_TOK:
      return Builder.getInt32Ty();
    case BOOL_TOK:
      return Builder.getInt1Ty();
    case FLOAT_TOK:
      return Builder.getFloatTy();
    case VOID_TOK:
      return Builder.getVoidTy();
  }
  return nullptr;
}

// Get the default value for an llvm::Type, which is defined as false for booleans, 0 for ints and 0.0 for floats
// Note this function should only be called with a boolean, int or float type - not void, since it doesn't have a value
static Constant *GetTypeDefaultVal(Type *t) {
  // convert to float
  if (t->isIntegerTy(1)) {
    return ConstantInt::get(TheContext, APInt(1, 0));
  }
  if (t->isIntegerTy(32)) {
    return ConstantInt::get(TheContext, APInt(32, 0));
  }
  return ConstantFP::get(TheContext, APFloat(0.0f)); // Already a float
}

// Cast the input llvm::Value to an llvm::Value of type bool (unsigned 1-bit integer)
Value *CastToBool(Value *v) {
  if (v->getType()->isIntegerTy(32)) {
    // Emit a comparison of the signed 32-bit int to a signed 32-bit 0 value, checking for non-equality, thus output is true (1) if the value is not equal to 0 and false (0) otherwise
    return Builder.CreateICmpNE(v, ConstantInt::get(Builder.getInt32Ty(), 0, true));
  }
  if (v->getType()->isFloatTy()) {
    // Emit floating point to unsigned int instruction
    return Builder.CreateFPToUI(v, Builder.getInt1Ty());
  }
  return v; // Already a bool
}

// Cast the input llvm::Value to an llvm::Value of type int (signed 32-bit integer)
Value *CastToInt(Value *v) {
  if (v->getType()->isIntegerTy(1)) {
    // Emit cast to a signed 32-bit integer instruction
    return Builder.CreateIntCast(v, Builder.getInt32Ty(), true);
  }
  if (v->getType()->isFloatTy()) {
    // Emit floating point to signed int instruction
    return Builder.CreateFPToSI(v, Builder.getInt32Ty());
  }
  return v; // Already an int
}

// Cast the input llvm::Value to an llvm::Value of type float (LLVM internal type)
Value *CastToFloat(Value *v) {
  if (v->getType()->isIntegerTy(1)) {
    // Emit unsigned integer to floating point instruction
    return Builder.CreateUIToFP(v, Builder.getFloatTy());
  }
  if (v->getType()->isIntegerTy(32)) {
    // Emit signed integer to floating point instruction
    return Builder.CreateSIToFP(v, Builder.getFloatTy());
  }
  return v; // Already a float
}

// Obtain the maximum of the two given llvm::Type's, where a float has the highest type, followed by int and finally bool with the lowest
// Note this ordering is in the ordering of upcasting, i.e. one can always upcast bool -> int and int -> float but not necessarily the other way round
Type *MaxType(Type *t1, Type *t2) {
  if (t1->isFloatTy() || t2->isFloatTy()) return Builder.getFloatTy();
  if (t1->isIntegerTy(32) || t2->isIntegerTy(32)) return Builder.getInt32Ty();
  return Builder.getInt1Ty();
}

// Cast the given llvm::Value to the given llvm::Type
Value *Cast(Value *v, Type *t) {
  if (t->isFloatTy()) return CastToFloat(v);
  if (t->isIntegerTy(32)) return CastToInt(v);
  return CastToBool(v);
}

// Upcast the given llvm::Value to the given llvm::Type, and if no upcasting is possible
// (i.e. only downcasting is possible, in the case the type to cast to has a lower rank than the type of the given value)
// then return nullptr.
Value *UpCast(Value *v, Type *target_type) {
  Type *val_type = v->getType();
  Type *max_type = MaxType(target_type, val_type);
  if (val_type != target_type) {
    if (val_type == max_type) {
      // Type of value is maximal and since types are not equal it's greater than the type to cast to. Cannot upcast, error.
      return nullptr;
    }
    // The type to cast to is maximal and thus greater than the type of value, thus we can upcast
    return Cast(v, target_type);
  }
  // Value is already the type to cast to, nothing to do
  return v;
}

// Print the given code generation error message to std::err and return a nullptr llvm::Value
// to allow `return PrintCodeGenerationError(...)` to print the error message and return nullptr from the caller method.
Value *PrintCodeGenerationError(std::string msg) {
  errs() << "Code generation error: " << msg << "\n";
  return nullptr;
}

//===----------------------------------------------------------------------===//
// AST Printer Helper Class
//===----------------------------------------------------------------------===//

// A serialisable nested collection (tree) of strings, i.e. a string with a collection of child strings
class StringCollection {
  std::string Str;
  std::vector<std::unique_ptr<StringCollection>> Children;
public:
  StringCollection(std::string str) : Str(str) {}
  // Add a collection of strings (node) to this string collection's children.
  void AddChild(std::unique_ptr<StringCollection> child) {
    Children.push_back(std::move(child));
  }
  // Recursively serialize this string collection (tree) by indenting the collection's string value by `ident` spaces
  // and indenting all of its children string collections by `ident_delta` spaces
  std::string ToString(int indent, int indent_delta) {
    std::stringstream ss;
    // Add `ident` spaces
    for (int i = 0; i < indent; i++) {
      ss << " ";
    }
    // Add the string value on this line
    ss << Str << "\n";
    // The indent level for the children is the current indentation level + the delta
    int child_indent = indent + indent_delta;
    // Write the serialization of each child to the stringstream
    for (auto&& child : Children) {
      std::string child_str = child->ToString(child_indent, indent_delta);
      ss << child_str;
    }
    // Return the serialised StringCollection
    return ss.str();
  }
};

//===----------------------------------------------------------------------===//
// AST and Code Generation
//===----------------------------------------------------------------------===//

/// ASTnode - Base class for all AST nodes.
class ASTnode {
public:
  virtual ~ASTnode() {}
  virtual Value *codegen();
  virtual std::unique_ptr<StringCollection> to_string() const;
};

// Variable declaration
class VarDeclASTnode : public ASTnode {
  TOKEN Type; // Not void type
public:
  std::string Var_Name;
  VarDeclASTnode(TOKEN type, std::string var_name) : Type(type), Var_Name(var_name) {}
  Value *codegen() override {
    // Get the current function being inserted into, which may be null in which case we're in global scope
    Function *theFunction = Builder.GetInsertBlock() ? Builder.GetInsertBlock()->getParent() : nullptr;
    // We're in global scope if we're not inserting into a function
    bool isGlobal = !theFunction;

    // Get llvm::Type of the variable declaration
    llvm::Type *type = GetTokenLLVMType(Type);

    if (isGlobal) {
      // In global scope. Check if the variable is already declared globally, in which case error
      if (GlobalNamedValues[Var_Name]) return PrintCodeGenerationError("Global variable with name " + Var_Name + " redeclared.");

      // Emit and initialise the global variable to the default value for its type.
      TheModule->getOrInsertGlobal(Var_Name, type);
      GlobalVariable *gVar = TheModule->getNamedGlobal(Var_Name);
      gVar->setInitializer(GetTypeDefaultVal(type)); 
      GlobalNamedValues[Var_Name] = gVar;
      return gVar;
    }
    // Is a local variable. Declare it.
    // Note we always allow the local variable to be declard here because duplicate declaration of local variables is checked within BlockASTnode::codegen, and local varable redeclaration is only an issue within the same block.
    // Note since local variables can override global variables, we don't error on that case.
    AllocaInst *alloca = CreateEntryBlockAlloca(theFunction, Var_Name, type);
    NamedValues[Var_Name] = alloca;
    return alloca;
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("variableDeclaration");
    str_base->AddChild(std::make_unique<StringCollection>("type=" + Type.lexeme));
    str_base->AddChild(std::make_unique<StringCollection>("variableName=" + Var_Name));
    return str_base;
  }
};

// Parameter
class ParamASTnode : public ASTnode {
public:
  TOKEN Type; // Not void
  std::string Param_Name;
  ParamASTnode(TOKEN type, std::string param_name) : Type(type), Param_Name(param_name) {}
  Value *codegen() override {
    // We delegate the code generation for all parameters of a function in FunDeclASTnode::codegen rather than on a per-parameter basis
    return nullptr;
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("param");
    str_base->AddChild(std::make_unique<StringCollection>("type=" + Type.lexeme));
    str_base->AddChild(std::make_unique<StringCollection>("name=" + Param_Name));
    return str_base;
  }
};

// Parameters
class ParamsASTnode : public ASTnode {
public:
  bool Is_Void; // Are the parameters "void"?
  std::vector<std::unique_ptr<ParamASTnode>> Param_List;
  ParamsASTnode(bool is_void, std::vector<std::unique_ptr<ParamASTnode>> param_list) : Is_Void(is_void), Param_List(std::move(param_list)) {}
  Value *codegen() override {
    // We delegate the code generation for the parameters of a function in FunDeclASTnode::codegen
    return nullptr;
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("param");
    if (Is_Void) {
      str_base->AddChild(std::make_unique<StringCollection>("void"));
      return str_base;
    }
    for (auto&& param : Param_List) {
      str_base->AddChild(param->to_string());
    }
    return str_base;
  }
};

// Extern function
class ExternASTnode : public ASTnode {
  TOKEN Return_Type;
  std::string Function_Name;
  std::unique_ptr<ParamsASTnode> Params;

public:
  ExternASTnode(TOKEN return_type, std::string function_name, std::unique_ptr<ParamsASTnode> params) : Return_Type(return_type), Function_Name(function_name), Params(std::move(params)) {}
  Value *codegen() override {
    // Make the function type
    std::vector<llvm::Type *> argsTypes;
    // Get the llvm::Type's of the parameters/arguments
    for (auto&& param : Params->Param_List) {
      llvm::Type *type = GetTokenLLVMType(param->Type);
      argsTypes.push_back(type);
    }
    // Get the llvm::Type of the return
    llvm::Type *return_type = GetTokenLLVMType(Return_Type);
    // Make the llvm::FunctionType
    FunctionType *functionType = FunctionType::get(return_type, argsTypes, false);
    // Make the llvm::Function specifing external linkage
    Function *function = Function::Create(functionType, Function::ExternalLinkage, Function_Name, TheModule.get());

    // Set names for all arguments
    unsigned i = 0;
    for (auto &arg : function->args())
      arg.setName(Params->Param_List[i++]->Param_Name);

    // Check the function isn't already declared
    if (Functions[Function_Name]) return PrintCodeGenerationError("Redefinition of function " + Function_Name);

    // Store the function
    return Functions[Function_Name] = function;
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("extern");
    str_base->AddChild(std::make_unique<StringCollection>("returnType=" + Return_Type.lexeme));
    str_base->AddChild(std::make_unique<StringCollection>("functionName=" + Function_Name));
    str_base -> AddChild(Params->to_string());
    return str_base;
  }
};

// Base class for priority 8 (least priority) expressions
class ExprASTnode : public ASTnode {
public:
 virtual ~ExprASTnode() {}
};


// List of arguments to a function call
class ArgListASTnode : public ASTnode {
public:
  std::vector<std::unique_ptr<ExprASTnode>> Args_Expr_List;
  ArgListASTnode(std::vector<std::unique_ptr<ExprASTnode>> args_expr_list): Args_Expr_List(std::move(args_expr_list)) {}
  Value *codegen() override {
    // We delegate the code generation of argument lists to FunctionCallElementASTnode::codegen
    return nullptr;
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("args");
    for (auto&& expr : Args_Expr_List) {
      str_base->AddChild(expr->to_string());
    }
    return str_base;
  }
};


// Base class for element AST nodes - priority 1 (highest priority) expressions
class ElementASTnode : public ASTnode {
public:
  virtual ~ElementASTnode() {}
};

// Prefix operator expressions - expressions with a unary ! or - as a prefix to an inner expression
class PrefixOpElementASTnode : public ElementASTnode {
  TOKEN Op; // may be - or !
  std::unique_ptr<ElementASTnode> Value_Element;
public:
  PrefixOpElementASTnode(TOKEN op, std::unique_ptr<ElementASTnode> value_element): Op(op), Value_Element(std::move(value_element)) {}
  Value *codegen() override {
    // Emit value
    Value *innerVal = Value_Element->codegen();
    if (!innerVal) return nullptr; // Propogate error

    if (Op.type == NOT) {
      // Is unary ! operator. Only booleans can be input and output from this operator, so cast the inner llvm::Value to a boolean (which we can always do)
      innerVal = CastToBool(innerVal);
      // Emit ! instruction
      return Builder.CreateNot(innerVal);
    }
    // Is unary - operator. If the inner llvm::Value is a boolean then upcast it to an integer since -false = -1 thus we must enter the integer domain.
    if (innerVal->getType()->isIntegerTy(1)) {
      innerVal = CastToInt(innerVal);
    }
    // The inner llvm::Value is either an integer or a float. Emit the ! operator respectively.
    if (innerVal->getType()->isIntegerTy(32)) {
      return Builder.CreateNeg(innerVal, "negtmp"); 
    }
    return Builder.CreateFNeg(innerVal, "fnegtmp");
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("unaryOpExpr");
    str_base->AddChild(std::make_unique<StringCollection>("op=" + Op.lexeme));
    str_base->AddChild(Value_Element->to_string());
    return str_base;
  };
};

// Parenthesis expression
class ParanthesisElementASTnode : public ElementASTnode {
  std::unique_ptr<ExprASTnode> Inner_Expr;
public:
  ParanthesisElementASTnode(std::unique_ptr<ExprASTnode> inner_expr) : Inner_Expr(std::move(inner_expr)) {}
  Value *codegen() override {
    // Paranthesis expressions simply exist to enforce precedence, but they emit just the code of the inner expression
    return Inner_Expr->codegen();
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("parenthesisExpr");
    str_base->AddChild(Inner_Expr->to_string());
    return str_base;
  };
};

// IDENT expression, which is a variable
class IdentElementASTnode : public ElementASTnode {
  std::string Var_Name;
public:
  IdentElementASTnode(std::string var_name) : Var_Name(var_name) {}
  Value *codegen() override {
    // Lookup the variable, preferring local over global variables. Emit load of the alloca or global variable respectively if exist.
    if (NamedValues[Var_Name]) return Builder.CreateLoad(NamedValues[Var_Name], Var_Name);
    if (GlobalNamedValues[Var_Name]) return Builder.CreateLoad(GlobalNamedValues[Var_Name]);
    return PrintCodeGenerationError("Undeclared variable name '" + Var_Name + "' in expression.");
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("identifierExpr");
    str_base->AddChild(std::make_unique<StringCollection>("varName=" + Var_Name));
    return str_base;
  }
};

class IntElementASTnode : public ElementASTnode {
  int Val;
public:
  IntElementASTnode(int value) : Val(value) {}
  Value *codegen() override {
    return ConstantInt::get(TheContext, APInt(32, Val));
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("int expr");
    str_base->AddChild(std::make_unique<StringCollection>("value=" + std::to_string(Val)));
    return str_base;
  };
};

class FloatElementASTnode: public ElementASTnode {
  float Val;
public:
  FloatElementASTnode(float value) : Val(value) {}
  Value *codegen() override {
    return ConstantFP::get(TheContext, APFloat(Val));
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("float expr");
    str_base->AddChild(std::make_unique<StringCollection>("value=" + std::to_string(Val)));
    return str_base;
  };
};

class BoolElementASTnode : public ElementASTnode {
  bool Val;
public:
  BoolElementASTnode(bool value) : Val(value) {}
  Value *codegen() override {
    return Val ? Builder.getTrue() : Builder.getFalse();
    // return ConstantInt::get(TheContext, APInt(1, Val ? 1 : 0));
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("bool expr");
    str_base->AddChild(std::make_unique<StringCollection>("value=" + std::to_string(Val)));
    return str_base;
  };
};

class FunctionCallElementASTnode : public ElementASTnode {
  std::string Function_Name_Identifier;
  std::unique_ptr<ArgListASTnode> Args;
public:
  FunctionCallElementASTnodestd::string function_name_identifier, std::unique_ptr<ArgListASTnode> args) : Function_Name_Identifier(function_name_identifier), Args(std::move(args)) {}
  Value *codegen() override {
    // std::vector<std::unique_ptr<ExprASTnode>> Args_Expr_List
    // Look up the name in the global module table.
    Function *CalleeF = TheModule->getFunction(Function_Name_Identifier);
    if (!CalleeF) {
      errs() << "Unknown function referenced " << Function_Name_Identifier;
      return nullptr;
    }

    // If argument mismatch error.
    if (CalleeF->arg_size() != Args->Args_Expr_List.size()) {
      errs() << "Incorrect # arguments passed";
      return nullptr;
    }

    std::vector<Value *> ArgsV;
    for (unsigned i = 0, e = Args->Args_Expr_List.size(); i != e; ++i) {
      Value *arg_val = Args->Args_Expr_List[i]->codegen();
      Type *arg_expected_type = CalleeF->getArg(i)->getType();
      // attempt to upcast the argument value to its expected type
      Value *upcast_arg_val = UpCast(arg_val, arg_expected_type);
      if (!upcast_arg_val) {
          errs() << "Argument of incorrece type.";
          return nullptr;
      }
      arg_val = upcast_arg_val;
      ArgsV.push_back(arg_val);
      if (!ArgsV.back())
        return nullptr;
    }

    return Builder.CreateCall(CalleeF, ArgsV);
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("function call expr");
    str_base->AddChild(std::make_unique<StringCollection>("functionName=" + Function_Name_Identifier));
    str_base->AddChild(Args->to_string());
    return str_base;
  };
};

// priority 2 subexpressions (*, /, %)
class FactorASTnode : public ASTnode {
  std::vector<std::unique_ptr<ElementASTnode>> Elements; // from left to right. non-empty
  std::vector<TOKEN> Operators; // between each element in Elements. may be *, / or %. may be empty.
public:
  FactorASTnode(std::vector<std::unique_ptr<ElementASTnode>> elements, std::vector<TOKEN> operators) : Elements(std::move(elements)), Operators(std::move(operators)) {}
  Value *codegen() override {
    Value *l = Elements[0]->codegen();
    if (!l) return nullptr;
    auto n = Elements.size();
    if (n == 1) return l;
    // promote bool to an int if we have one
    if (l->getType()->isIntegerTy(1)) {
      l = CastToInt(l);
    }
    for (unsigned i = 1; i < n; i++) {
      TOKEN op_tok = Operators[i - 1];
      Value *r = Elements[i]->codegen();
      if (!r) return nullptr;
      if (op_tok.type == MOD && !(l->getType()->isIntegerTy(32) && r->getType()->isIntegerTy(32))) { // if the operator is % and we have both integer arguments, this is an error 
        errs() << "Mod with non-integer operands.";
        return nullptr;
      }
      // promote to max type
      Type *max_type = MaxType(l->getType(), r->getType());
      if (l->getType() != max_type) l = Cast(l, max_type);
      else if (r->getType() != max_type) r = Cast(r, max_type);
      // l and r have the same type
      bool int_op = max_type->isIntegerTy();
      switch (op_tok.type) {
        case ASTERIX:
          l = int_op ? Builder.CreateMul(l, r, "multmp") : Builder.CreateFMul(l, r, "multmp");
          break;
        case DIV:
          l = int_op ? Builder.CreateSDiv(l, r, "divtmp") : Builder.CreateFDiv(l, r, "divtmp");
          break;
        case MOD:
          // guaranteed to be both ints
          l = Builder.CreateSRem(l, r, "modtmp");
          break;
        default: // just to satify c++ compiler
          return nullptr;
      }
    }
    return l;
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("factor expr (*, /, %)");
    str_base->AddChild(Elements[0]->to_string());
    // weave the operators between the elements
    for (int i = 1; i < Elements.size(); i++) {
      str_base->AddChild(std::make_unique<StringCollection>("op=" + Operators[i - 1].lexeme));
      str_base->AddChild(Elements[i]->to_string());
    }
    return str_base;
  };
};

// priority 3 subexpressions (+, -)
class SubexprASTnode : public ASTnode {
  std::vector<std::unique_ptr<FactorASTnode>> Factors; // from left to right. non-empty
  std::vector<TOKEN> Operators; // between each factor in Factors. may be + or -. may be empty.
public:
  SubexprASTnode(std::vector<std::unique_ptr<FactorASTnode>> factors, std::vector<TOKEN> operators) : Factors(std::move(factors)), Operators(std::move(operators)) {}
  Value *codegen() override {
    Value *l = Factors[0]->codegen();
    if (!l) return nullptr;
    auto n = Factors.size();
    if (n == 1) return l;
    // promote bool to int if we have one
    if (l->getType()->isIntegerTy(1)) {
      l = CastToInt(l);
    }
    for (unsigned i = 1; i < Factors.size(); i++) {
      TOKEN op_tok = Operators[i - 1];
      Value *r = Factors[i]->codegen();
      if (!r) return nullptr;
      // promote the least type
      Type *max_type = MaxType(l->getType(), r->getType());
      if (l->getType() != max_type) l = Cast(l, max_type);
      else if (r->getType() != max_type) r = Cast(r, max_type);
      // l and r are the same type
      bool int_op = max_type->isIntegerTy();
      switch (op_tok.type) {
        case PLUS:
          l = int_op ? Builder.CreateAdd(l, r, "addtmp") : Builder.CreateFAdd(l, r, "addtmp");
          break;
        case MINUS:
          l = int_op ? Builder.CreateSub(l, r, "subtmp") : Builder.CreateFSub(l, r, "subtmp");
          break;
        default: // just to satify c++ compiler
          return nullptr;
      }
    }
    return l;
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("subexpr expr (+, -)");
    str_base->AddChild(Factors[0]->to_string());
    // weave the operators between the factors
    for (int i = 1; i < Factors.size(); i++) {
      str_base->AddChild(std::make_unique<StringCollection>("op=" + Operators[i - 1].lexeme));
      str_base->AddChild(Factors[i]->to_string());
    }
    return str_base;
  };
};

// priority 4 subexpressions (relations <=, <, >=, >)
class RelASTnode : public ASTnode {
  std::vector<std::unique_ptr<SubexprASTnode>> Subexprs; // from left to right. non-empty
  std::vector<TOKEN> Operators; // between each subexpr in Subexprs. may be <=, <, > or >=. may be empty.
public:
  RelASTnode(std::vector<std::unique_ptr<SubexprASTnode>> subexprs, std::vector<TOKEN> operators) : Subexprs(std::move(subexprs)), Operators(std::move(operators)) {}
  Value *codegen() override {
    Value *l = Subexprs[0]->codegen();
    if (!l) return nullptr;
    auto n = Subexprs.size();
    if (n == 1) return l;
    for (unsigned i = 1; i < n; i++) {
      TOKEN op_tok = Operators[i - 1];
      Value *r = Subexprs[i]->codegen();
      if (!r) return nullptr;
      // l and r must be the same type. bring the type higher if not
      Type *max_type = MaxType(l->getType(), r->getType());
      if (l->getType() != max_type) l = Cast(l, max_type);
      else if (r->getType() != max_type) r = Cast(r, max_type);
      // l and r are now the same type
      bool int_op = r->getType()->isIntegerTy();
      switch (op_tok.type) {
        // CreateFCmpULE, CreateFCmpULT, CreateFCmpUGE, CreateFCmpUGT
        case LE:
          l = int_op ? Builder.CreateICmpULE(l, r, "letmp") : Builder.CreateFCmpULE(l, r, "letmp");
          break;
        case GE:
          l = int_op ? Builder.CreateICmpUGE(l, r, "getmp") : Builder.CreateFCmpUGE(l, r, "getmp");
          break;
        case LT:
          l = int_op ? Builder.CreateICmpULT(l, r, "lttmp") : Builder.CreateFCmpULT(l, r, "lttmp");
          break;
        case GT:
          l = int_op ? Builder.CreateICmpUGT(l, r, "gttmp") : Builder.CreateFCmpUGT(l, r, "gttmp");
          break;
        default: // just to satify c++ compiler
          return nullptr;
      }
    }
    // result is always a bool
    return CastToBool(l);
    // return Builder.CreateUIToFP(l, Type::getFloatTy(TheContext));
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("rel expr (<=, <, >=, >)");
    str_base->AddChild(Subexprs[0]->to_string());
    // weave the operators between the subexprs
    for (int i = 1; i < Subexprs.size(); i++) {
      str_base->AddChild(std::make_unique<StringCollection>("op=" + Operators[i - 1].lexeme));
      str_base->AddChild(Subexprs[i]->to_string());
    }
    return str_base;
  };
};

// priority 5 subexpressions (equivalence ==)
class EquivASTnode : public ASTnode {
  std::vector<std::unique_ptr<RelASTnode>> Rels; // from left to right. non-empty
  std::vector<TOKEN> Operators; // between each rel in Rels. may be == or !=. may be empty.
public:
  EquivASTnode(std::vector<std::unique_ptr<RelASTnode>> rels, std::vector<TOKEN> operators) : Rels(std::move(rels)), Operators(std::move(operators)) {}
  Value *codegen() override {
    Value *l = Rels[0]->codegen();
    if (!l) return nullptr;
    auto n = Rels.size();
    if (n == 1) return l;
    for (unsigned i = 1; i < n; i++) {
      TOKEN op_tok = Operators[i - 1];
      Value *r = Rels[i]->codegen();
      if (!r) return nullptr;
      // promote to max type https://stackoverflow.com/a/24067599
      Type *max_type = MaxType(l->getType(), r->getType());
      if (l->getType() != max_type) l = Cast(l, max_type);
      else if (r->getType() != max_type) r = Cast(r, max_type);
      // l and r and the same type
      bool int_op = max_type->isIntegerTy();
      switch (op_tok.type) {
        // CreateFCmpUEQ, CreateFCmpUNE
        case EQ:
          l = int_op ? Builder.CreateICmpEQ(l, r, "eqtmp") : Builder.CreateFCmpUEQ(l, r, "eqtmp");
          break;
        case NE:
          l = int_op ? Builder.CreateICmpNE(l, r, "netmp") : Builder.CreateFCmpUNE(l, r, "netmp");
          break;
        default: // just to satify c++ compiler
          return nullptr;
      }
    }
    std::cout << "\requiv expr codegen\n";
    return Builder.CreateSIToFP(l, Type::getFloatTy(TheContext)); // convert to  float
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("equiv expr (==, !=)");
    str_base->AddChild(Rels[0]->to_string());
    // weave the operators between the rels
    for (int i = 1; i < Rels.size(); i++) {
      str_base->AddChild(std::make_unique<StringCollection>("op=" + Operators[i - 1].lexeme));
      str_base->AddChild(Rels[i]->to_string());
    }
    return str_base;
  };
};

// priority 6 subexpressions (&&)
class TermASTnode : public ASTnode {
  std::vector<std::unique_ptr<EquivASTnode>> Equivs; // from left to right. non-empty
  // we void the Operators vector because we know the only operator is && and it is applied between each equiv in Equivs.
public:
  TermASTnode(std::vector<std::unique_ptr<EquivASTnode>> equivs) : Equivs(std::move(equivs)) {}
  Value *codegen() override {
    Value *l = Equivs[0]->codegen();
    if (!l) return nullptr;
    auto n = Equivs.size();
    if (n == 1) return l;
    l = CastToBool(l);
    for (unsigned i = 1; i < n; i++) {
      if ((static_cast<ConstantInt *>(l))->isZero()) break;
      l = Equivs[i]->codegen();
      if (!l) return nullptr;
      l = CastToBool(l);
    }
    return l;
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("term expr (&&)");
    for (int i = 0; i < Equivs.size(); i++) {
      str_base->AddChild(Equivs[i]->to_string());
    }
    return str_base;
  };
};

// priority 7 subexpressions (||)
class RValASTnode : public ASTnode {
  std::vector<std::unique_ptr<TermASTnode>> Terms; // from left to right. non-empty
  // we void the Operators vector because we know the only operator is || and it is applied between each term in Terms.
public:
  RValASTnode(std::vector<std::unique_ptr<TermASTnode>> terms) : Terms(std::move(terms)) {}
  Value *codegen() override {
    Value *l = Terms[0]->codegen();
    if (!l) return nullptr;
    auto n = Terms.size();
    if (n == 1) return l;
    l = CastToBool(l);
    for (unsigned i = 1; i < n; i++) {
      if ((static_cast<ConstantInt *>(l))->isOne()) break;
      l = Terms[i]->codegen();
      if (!l) return nullptr;
      l = CastToBool(l);
    }
    return l;
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("rval expr (||)");
    for (int i = 0; i < Terms.size(); i++) {
      str_base->AddChild(Terms[i]->to_string());
    }
    return str_base;
  };
};

// priority 8 [least] assignment subexpression
class AssignExprASTnode : public ExprASTnode {
  std::string Var_Name_Identifier;
  std::unique_ptr<ExprASTnode> Value_Expr;
public:
  AssignExprASTnode(std::string var_name_identifier, std::unique_ptr<ExprASTnode> value_expr) : Var_Name_Identifier(std::move(var_name_identifier)), Value_Expr(std::move(value_expr)) {}
  Value *codegen() override {
    // Codegen the RHS.
    Value *Val = Value_Expr->codegen();
    if (!Val) return nullptr; // pass through error

    // lookup variable declaration, prioritising local over global
    if (NamedValues[Var_Name_Identifier]) {
      // attempt to upcast the value to the type of the variable
      Value *upcast_val = UpCast(Val, NamedValues[Var_Name_Identifier]->getType()->getPointerElementType());
      if (!upcast_val) {
        errs() << "RHS of assignment does not match type of LHS. " << Var_Name_Identifier ;
        return nullptr;
      }
      Val = upcast_val;
      Builder.CreateStore(Val, NamedValues[Var_Name_Identifier]);
    }
    else if (GlobalNamedValues[Var_Name_Identifier]) {
      // attempt to upcast the value to the type of the variable
      Value *upcast_val = UpCast(Val, GlobalNamedValues[Var_Name_Identifier]->getType()->getPointerElementType());
      if (!upcast_val) {
        errs() << "RHS of assignment does not match type of LHS. " << Var_Name_Identifier ;
        return nullptr;
      }
      Val = upcast_val;
      Builder.CreateStore(Val, GlobalNamedValues[Var_Name_Identifier]);
    }
    else {
      errs() << "Unknown variable name (assign) " << Var_Name_Identifier;
      return nullptr;
    }
    
    return Val;
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("assign expr (=)");
    str_base->AddChild(std::make_unique<StringCollection>("varName=" + Var_Name_Identifier));
    auto value_base = std::make_unique<StringCollection>("value");
    value_base->AddChild(Value_Expr->to_string());
    str_base->AddChild(std::move(value_base));
    return str_base;
  };
};

// priority 8 [least] rval delegation subexpression
class RValExprASTnode : public ExprASTnode {
  std::unique_ptr<RValASTnode> RVal;

public:
  RValExprASTnode(std::unique_ptr<RValASTnode> rval) : RVal(std::move(rval)) {}
  Value *codegen() override {
    return RVal->codegen();
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("rval delegation expr");
    str_base->AddChild(RVal->to_string());
    return str_base;
  };
};

enum class StmtType {Base, Expr, Block, If, While, Return};

// Base class for stmt
class StmtASTnode : public ASTnode {
public:
  virtual ~StmtASTnode() {}
  virtual StmtType type() const {
    return StmtType::Base;
  }
};

class ExprStmtASTnode : public StmtASTnode {
public:
  std::unique_ptr<ExprASTnode> Expr; // may be null
  ExprStmtASTnode(std::unique_ptr<ExprASTnode> expr) : Expr(std::move(expr)) {}
  Value *codegen() override {
    if (Expr) return Expr->codegen();
    return 0; // don't return null because this is not an error
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("expr statement");
    if (Expr) str_base->AddChild(Expr->to_string());
    return str_base;
  };
  StmtType type() const override {
    return StmtType::Expr;
  }
};

class ReturnStmtASTnode : public StmtASTnode {
  std::unique_ptr<ExprStmtASTnode> Return_Expr_Stmt;

public:
  ReturnStmtASTnode(std::unique_ptr<ExprStmtASTnode> return_expr_stmt): Return_Expr_Stmt(std::move(return_expr_stmt)) {}
  Value *codegen() override {
    Function *TheFunction = Builder.GetInsertBlock()->getParent();
    Type *return_type = TheFunction->getReturnType();

    if (Return_Expr_Stmt->Expr) { // have a return value
      // evaluate return value
      Value *return_val = Return_Expr_Stmt->Expr->codegen();
      // attempt to upcast the return val to the return type of the function
      Value *upcast_return_val = UpCast(return_val, return_type);
      if (!upcast_return_val) {
        errs() << "Return expression does not match return type of function.";
        return nullptr;
      }
      return_val = upcast_return_val;
      return Builder.CreateRet(return_val);
    }
    else { // no return value - return void
      if (!return_type->isVoidTy()) {
        errs() << "Missing return statement.";
        return nullptr;
      } 
      return Builder.CreateRetVoid();
    }
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("return statement");
    str_base->AddChild(Return_Expr_Stmt->to_string());
    return str_base;
  };
  StmtType type() const override {
    return StmtType::Return;
  }
};

class BlockASTnode : public StmtASTnode {
  std::vector<std::unique_ptr<VarDeclASTnode>> Local_Decls;

public:
  std::vector<std::unique_ptr<StmtASTnode>> Stmts;
  BlockASTnode(std::vector<std::unique_ptr<VarDeclASTnode>> local_decls, std::vector<std::unique_ptr<StmtASTnode>> stmts) : Local_Decls(std::move(local_decls)), Stmts(std::move(stmts)) {}
  Value *codegen() override {
    // return the return value
    // TODO: in function decl check block contains a return stmt, or that all of its block otherwise issue
    // the local_decls are local to this block, so after codegening the block, remove them from local scope by restoring previous local scope

    // any Local_Decls of the same variable twice are errors
    // if we have a Local_Decl of a variable, then after the block we will revert the variable to its old value. otherwise, we won't (since it's not redeclared in the block, it's changing the outer local scope).

    // any Local_Decls of the same variable twice are errors
    int numDecls = Local_Decls.size();
    for (unsigned i = 0; i < numDecls; i++) {
      for (unsigned j = i + 1; j < numDecls; j++) {
        if (Local_Decls[i]->Val == Local_Decls[j]->Val) {
          errs() << "Local redeclaration of " << Local_Decls[i]->Val;
          return nullptr;
        }
      }
    }

    // all local_decls must have their value reset after the block. gather the original values.
    std::vector<AllocaInst *> old_bindings; // the old bindings for newly declared variable in this block
    std::vector<bool> old_bindings_local_scope; // whether each old_binding is local scope or not (otherwise global)
    for (unsigned i = 0; i < numDecls; i++) {
      auto var_name = Local_Decls[i]->Val;
      auto old_val = NamedValues[var_name] ? NamedValues[var_name] : nullptr;
      bool old_local = NamedValues[var_name] || (!NamedValues[var_name] && !GlobalNamedValues[var_name]);
      old_bindings.push_back(old_val);
      old_bindings_local_scope.push_back(old_local);
      // we may want to revert the variable's value to nothing (null) after, but specifically the value in the local variables map since the new var will be a local var
      if (!Local_Decls[i]->codegen()) return nullptr;
    }

    // codegen each declaration
    for (auto&& decl : Local_Decls) {
      if (!decl->codegen()) {
        return nullptr; // propogate
      }
    }

    // codegen each statement
    for (auto&& stmt : Stmts) {
      if (!stmt->codegen()) {
        return nullptr; // propogate
      }
    }

    std::cout << "\nSTMT done codegennign stmts\n";

    // restore values for variables
    for (unsigned i = 0; i < numDecls; i++) {
      auto var_name = Local_Decls[i]->Val;
      auto old_binding = old_bindings[i];
      if (old_bindings_local_scope[i]) { // old binding was local scope
        NamedValues[var_name] = old_binding;
      }
      else { // old binding was global scope. remove the local scope value for the variable
        NamedValues.erase(var_name);
      }
    }

    std::cout << "\nSTMT done restoring local vars\n";

    // for each local_decl, if the var name is already a local variable then this is a semantic error. note this is caught later on anyway in VarDeclASTNode::codegen - yay.
    // code gen each Local_Decl, storing beforehand the pre values for the vars and restoring them after this whole function
    // codegen each stmt in-tern. note the stmt may be a block iself, so codegenning a block (this function) should ensure the postcondition removes the side-effects (the local_decls brought into scope) as achived by ^line.

    return Constant::getNullValue(Type::getInt1Ty(TheContext));
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("block");
    auto local_decls_base = std::make_unique<StringCollection>("local decls");
    for (auto&& local_decl : Local_Decls) {
      local_decls_base->AddChild(local_decl->to_string());
    }
    str_base->AddChild(std::move(local_decls_base));
    auto stmts_base = std::make_unique<StringCollection>("statements");
    for (auto&& stmt : Stmts) {
      stmts_base->AddChild(stmt->to_string());
    }
    str_base->AddChild(std::move(stmts_base));
    return str_base;
  };
  StmtType type() const override {
    return StmtType::Block;
  }
};

class IfStmtASTnode : public StmtASTnode {
  std::unique_ptr<ExprASTnode> Condition_Expr;

public:
  std::unique_ptr<BlockASTnode> If_Body;
  std::unique_ptr<BlockASTnode> Else_Body; // may be null for no else
  IfStmtASTnode(std::unique_ptr<ExprASTnode> condition_expr, std::unique_ptr<BlockASTnode> if_body, std::unique_ptr<BlockASTnode> else_body): Condition_Expr(std::move(condition_expr)), If_Body(std::move(if_body)), Else_Body(std::move(else_body)) {}
  Value *codegen() override {
    Value *CondV = Condition_Expr->codegen();
    if (!CondV)
      return nullptr;

    if (CondV->getType()->isVoidTy()) { // can never be cast to a bool, error
      errs() << "Void condition in if.";
      return nullptr;
    }
    // Convert condition to a bool by comparing non-equal to 0.0.
    CondV = CastToBool(CondV);
    // Builder.CreateFCmpONE(
    //     CastToFloat(CondV), ConstantFP::get(TheContext, APFloat(0.0f)), "ifcond");

    Function *TheFunction = Builder.GetInsertBlock()->getParent();

    // Create blocks for the then and else cases.  Insert the 'then' block at the
    // end of the function.
    BasicBlock *ThenBB = BasicBlock::Create(TheContext, "then", TheFunction);
    BasicBlock *ElseBB = BasicBlock::Create(TheContext, "else");
    BasicBlock *MergeBB = BasicBlock::Create(TheContext, "ifcont");

    Builder.CreateCondBr(CondV, ThenBB, ElseBB);

    // Emit then value.
    Builder.SetInsertPoint(ThenBB);

    Value *ThenV = If_Body->codegen();
    if (!ThenV)
      return nullptr;

    Builder.CreateBr(MergeBB);

    // Emit else block.
    TheFunction->getBasicBlockList().push_back(ElseBB);
    Builder.SetInsertPoint(ElseBB);
    if (Else_Body) {
      Value *ElseV = Else_Body->codegen();
      if (!ElseV)
        return nullptr;
    }
    Builder.CreateBr(MergeBB);
    
    // Emit merge block.
    TheFunction->getBasicBlockList().push_back(MergeBB);
    Builder.SetInsertPoint(MergeBB);
    return Constant::getNullValue(Type::getInt1Ty(TheContext));
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("if statement");
    auto condition_base = std::make_unique<StringCollection>("condition");
    condition_base->AddChild(Condition_Expr->to_string());
    str_base->AddChild(std::move(condition_base));
    auto if_body_base = std::make_unique<StringCollection>("if body:");
    if_body_base->AddChild(If_Body->to_string());
    str_base->AddChild(std::move(if_body_base));
    if (Else_Body) {
      auto else_body_base = std::make_unique<StringCollection>("else body:");
      else_body_base->AddChild(Else_Body->to_string());
      str_base->AddChild(std::move(else_body_base));
    }
    return str_base;
  };
  StmtType type() const override {
    return StmtType::If;
  }
};

class WhileStmtASTnode : public StmtASTnode {
  std::unique_ptr<ExprASTnode> Condition_Expr;
  std::unique_ptr<StmtASTnode> Body_Stmt;

public:
  WhileStmtASTnode(std::unique_ptr<ExprASTnode> condition_expr, std::unique_ptr<StmtASTnode> body_stmt): Condition_Expr(std::move(condition_expr)), Body_Stmt(std::move(body_stmt)) {}
  Value *codegen() override {
    Function *TheFunction = Builder.GetInsertBlock()->getParent();

    BasicBlock *LoopCondBB = BasicBlock::Create(TheContext, "loopcond", TheFunction);
    BasicBlock *LoopBodyBB = BasicBlock::Create(TheContext, "loopbody");
    BasicBlock *EndBB = BasicBlock::Create(TheContext, "loopend");

    // Create a branch from the current block to the loop condition
    Builder.CreateBr(LoopCondBB);

    Builder.SetInsertPoint(LoopCondBB);

    // emit condition
    Value *CondV = Condition_Expr->codegen();
    if (!CondV)
      return nullptr;

    if (CondV->getType()->isVoidTy()) { // can never be cast to a bool, error
      errs() << "Void condition in while.";
      return nullptr;
    }

    // Convert condition to a bool by comparing non-equal to 0.0.
    CondV = CastToBool(CondV);
    // CondV = Builder.CreateFCmpONE(
    //     CondV, ConstantFP::get(TheContext, APFloat(0.0f)), "loopcond");

    // if the condition is true then branch to the loop body, otherwise branch to the end of the loop
    Builder.CreateCondBr(CondV, LoopBodyBB, EndBB);

    // Emit body
    TheFunction->getBasicBlockList().push_back(LoopBodyBB);
    Builder.SetInsertPoint(LoopBodyBB);

    Value *BodyV = Body_Stmt->codegen();
    if (!BodyV)
      return nullptr;

    // Unconditionally branch from the end of the loop body to the condition block again.
    Builder.CreateBr(LoopCondBB);

    // Emit end block.
    TheFunction->getBasicBlockList().push_back(EndBB);
    Builder.SetInsertPoint(EndBB);

    return CondV;
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("while statement");
    auto condition_base = std::make_unique<StringCollection>("condition");
    condition_base->AddChild(Condition_Expr->to_string());
    str_base->AddChild(std::move(condition_base));
    auto body_base = std::make_unique<StringCollection>("body");
    body_base->AddChild(Body_Stmt->to_string());
    str_base->AddChild(std::move(body_base));
    return str_base;
  };
  StmtType type() const override {
    return StmtType::While;
  }
};

bool GotReturnFromAllPaths(BlockASTnode* body) {
  for (auto&& stmt : body->Stmts) {
    auto stmt_type = stmt->type();
    if (stmt_type == StmtType::Return) return true;
    if (stmt_type == StmtType::Block) {
      auto block_stmt = static_cast<BlockASTnode*>(stmt.get());
      if (GotReturnFromAllPaths(block_stmt)) return true;
    }
    if (stmt_type == StmtType::If) {
      auto if_stmt = static_cast<IfStmtASTnode*>(stmt.get());
      if (!if_stmt->Else_Body) continue;
      if (GotReturnFromAllPaths(if_stmt->If_Body.get()) && GotReturnFromAllPaths(if_stmt->Else_Body.get())) return true;
    }
  }
  return false;
}

// may contain void
class FunDeclASTnode : public ASTnode {
  TOKEN Return_Type; // may be void
  std::string Name;
  std::unique_ptr<ParamsASTnode> Params;
  std::unique_ptr<BlockASTnode> Body; // Block

public:
  FunDeclASTnode(TOKEN return_type, std::string name, std::unique_ptr<ParamsASTnode> params, std::unique_ptr<BlockASTnode> body) : Return_Type(return_type), Name(name), Params(std::move(params)), Body(std::move(body)) {}
  Value *codegen() override {
    // Make the function type:  double(double,double) etc.
    std::vector<llvm::Type *> args_types;
    for (auto&& param : Params->Param_List) {
      // get type of the param
      llvm::Type *ty = GetTokenLLVMType(param->Type);
      args_types.push_back(ty);
    }
    llvm::Type *return_type = GetTokenLLVMType(Return_Type);
    FunctionType *FT =
        FunctionType::get(return_type, args_types, false);

    Function *F =
        Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());

    // Set names for all arguments.
    unsigned Idx = 0;
    for (auto &arg : F->args())
      arg.setName(Params->Param_List[Idx++]->Val);


    // now we have the function prototype F
    Function *TheFunction = F;

    // check the function isn't already declared
    if (Functions[Name]) {
      errs() << "Cannot redefine function " << Name;
      return nullptr;
    }

    // store the function
    Functions[Name] = F;

    // Create a new basic block to start insertion into.
    BasicBlock *BB = BasicBlock::Create(TheContext, "entry", TheFunction);
    Builder.SetInsertPoint(BB);

    // Record the function arguments in the NamedValues map.
    NamedValues.clear();
    Idx = 0;
    for (auto &Arg : TheFunction->args()) {
      // Create an alloca for this variable.
      llvm:Type *ty = GetTokenLLVMType(Params->Param_List[Idx]->Type);
      std::string name = Params->Param_List[Idx++]->Val;
      AllocaInst *Alloca = CreateEntryBlockAlloca(TheFunction, name, ty);

      // Store the initial value into the alloca.
      Builder.CreateStore(&Arg, Alloca);

      // Add arguments to variable symbol table.
      NamedValues[name] = Alloca;
    }

    if (Value *RetVal = Body->codegen()) {
      // RETURN CHECK: Check that all code paths eventually have a return.
      // rec: if return type is not void, check current block has a return. if not, check current block has an if and an else, both containing returns (recursively). otherwise we have no return thus error.
      if (Return_Type.type != VOID_TOK && !GotReturnFromAllPaths(Body.get())) {
        errs() << "Not all code paths return a value.";
        return nullptr; 
      }

      // Validate the generated code, checking for consistency.
      verifyFunction(*TheFunction);

      // add void return if a void function
      if (return_type->isVoidTy()) {
        Builder.CreateRetVoid();
      }
      else {
        Builder.CreateRet(GetTypeDefaultVal(return_type));
      }

      return TheFunction;
    }

    // Error reading body, remove function.
    TheFunction->eraseFromParent();
    return nullptr;
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("function declaration");
    str_base->AddChild(std::make_unique<StringCollection>("returnType=" + Return_Type.lexeme));
    str_base->AddChild(std::make_unique<StringCollection>("name=" + Name));
    str_base->AddChild(Params->to_string());
    auto body_base = std::make_unique<StringCollection>("body");
    body_base->AddChild(Body->to_string());
    str_base->AddChild(std::move(body_base));
    return str_base;
  };
};

class DeclASTnode : public ASTnode {
  std::unique_ptr<VarDeclASTnode> Var_Decl;
  std::unique_ptr<FunDeclASTnode> Fun_Decl;
  bool Is_Var_Decl;
public:
  DeclASTnode(std::unique_ptr<VarDeclASTnode> var_decl, std::unique_ptr<FunDeclASTnode> fun_decl, bool is_var_decl) : Var_Decl(std::move(var_decl)), Fun_Decl(std::move(fun_decl)), Is_Var_Decl(is_var_decl) {}
  Value *codegen() override {
    return Is_Var_Decl ? Var_Decl->codegen() : Fun_Decl->codegen();
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("declaration");
    str_base->AddChild(Is_Var_Decl ? Var_Decl->to_string() : Fun_Decl->to_string());
    return str_base;
  };
};

class ProgramASTnode : public ASTnode {
  std::vector<std::unique_ptr<ExternASTnode>> Extern_List;
  std::vector<std::unique_ptr<DeclASTnode>> Decl_List;
public:
  ProgramASTnode(std::vector<std::unique_ptr<ExternASTnode>> extern_list, std::vector<std::unique_ptr<DeclASTnode>> decl_list) : Extern_List(std::move(extern_list)), Decl_List(std::move(decl_list)) {}
  Value *codegen() override {
    // codegen each extern and decl
    for (auto&& externn : Extern_List) {
      if (!externn->codegen()) return nullptr;
    }
    for (auto&& decl : Decl_List) {
      if (!decl->codegen()) return nullptr;
    }
    return Constant::getNullValue(Type::getInt1Ty(TheContext));
  }
  std::unique_ptr<StringCollection> to_string() const override {
    auto str_base = std::make_unique<StringCollection>("program");
    auto externs_base = std::make_unique<StringCollection>("externs");
    for (auto&& externn : Extern_List) {
      externs_base->AddChild(externn->to_string());
    }
    str_base->AddChild(std::move(externs_base));
    auto decls_base = std::make_unique<StringCollection>("declarations");
    for (auto&& decl : Decl_List) {
      decls_base->AddChild(decl->to_string());
    }
    str_base->AddChild(std::move(decls_base));
    return str_base;
  };
};

/* add other AST nodes as nessasary */

//===----------------------------------------------------------------------===//
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

void PrintParserError(std::string msg) {
  errs() << "Parser error on line " << lineNo << " (lexeme: '" << CurTok.lexeme << "'): " << msg << "\n";
}

bool TokenContains(std::vector<TOKEN_TYPE> allowed_tokens, int token) 
{
  for (auto allowed_token : allowed_tokens) {
    if (allowed_token == token) return true;
  }
  return false;
}

/* Add function calls for each production */

// parses ("int" | "float" | "bool"), and if can_be_void, also (| "void")
TOKEN ParseType(bool can_be_void, std::string production_name) {
  std::vector<TOKEN_TYPE> legal_values_base = {INT_TOK, FLOAT_TOK, BOOL_TOK};
  if (!TokenContains(legal_values_base, CurTok.type) && (!can_be_void || CurTok.type != VOID_TOK)) {
    std::stringstream ss;
    ss << "Expected " << production_name << " to be one of 'int', 'float', 'bool'" << (can_be_void ? ", 'void'" : "") << ".";
    PrintParserError(ss.str());
    return CurTok;
  }
  // eat the type
  auto type = CurTok;
  getNextToken();
  return type;
}

// param ::= var_type IDENT
std::unique_ptr<ParamASTnode> ParseParam() {
  // parse the var_type
  auto type = ParseType(false, "var_type"); // cannot be void

  // eat the identifier which is the variable name
  if (CurTok.type != IDENT) {
    PrintParserError("Expected an identifier to follow the type of a var_decl.");
    return nullptr;
  }
  auto name = IdentifierStr;
  getNextToken();

  return std::make_unique<ParamASTnode>(type, name);
}

/* params ::= param_list  
          |  "void" | epsilon 
  param_list ::= param param_list2
  param_list2 ::= "," param param_list | epsilon */
std::unique_ptr<ParamsASTnode> ParseParams() {
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
    return std::make_unique<ParamsASTnode>(false, std::move(param_list));
  }
  if (CurTok.type == VOID_TOK) { // is just void
    // eat void
    getNextToken();
    return std::make_unique<ParamsASTnode>(true, std::move(std::vector<std::unique_ptr<ParamASTnode>>()));
  }
  if (CurTok.type == RPAR) { // current token is in follow of params, thus do nothing but is still valid production
    return std::make_unique<ParamsASTnode>(false, std::move(std::vector<std::unique_ptr<ParamASTnode>>()));
  }
  PrintParserError("Expected params to be either a list of param declarations, 'void', or empty, but is neither.");
  return nullptr;
}

// var_decl ::= var_type IDENT ";" 
std::unique_ptr<VarDeclASTnode> ParseVarDecl() {
  // parse the var_type
  auto type = ParseType(false, "var_decl"); // cannot be void

  // eat the identifier which is the variable name
  if (CurTok.type != IDENT) {
    PrintParserError("Expected an identifier to follow the type of a var_decl.");
    return nullptr;
  }
  auto name = IdentifierStr;
  getNextToken();

  // eat the ';'
  if (CurTok.type != SC) {
    PrintParserError("Expected ';' to follow the variable name in a var_decl.");
    return nullptr;
  }
  getNextToken();

  return std::make_unique<VarDeclASTnode>(type, name);
}

std::unique_ptr<BlockASTnode> ParseBlock(); // forward declaring ParseBlock due to cyclic dependency between ParseFunDecl and ParseBlock

// fun_decl ::= type_spec IDENT "(" params ")" block
std::unique_ptr<FunDeclASTnode> ParseFunDecl() {
  // parse type_spec
  auto return_type = ParseType(true, "type_spec"); // can be void

  // eat the identifier which is the function name
  if (CurTok.type != IDENT) {
    PrintParserError("Expected an identifier to follow the type of a fun_decl.");
    return nullptr;
  }
  auto name = IdentifierStr;
  getNextToken();

  // eat the '('
  if (CurTok.type != LPAR) {
    PrintParserError("Expected '(' to follow the function name in a fun_decl.");
    return nullptr;
  }
  getNextToken();

  auto params = ParseParams();

  // eat the ')'
  if (CurTok.type != RPAR) {
    PrintParserError("Expected ')' to follow params in a fun_decl.");
    return nullptr;
  }
  getNextToken();

  auto body = ParseBlock();

  return std::make_unique<FunDeclASTnode>(CurTok, return_type, name, std::move(params), std::move(body));
}

/* decl ::= var_decl 
        |  fun_decl */
std::unique_ptr<DeclASTnode> ParseDecl() {
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
    PrintParserError("Expected var_decl or fun_decl in decl.");
  }
  return nullptr;
}

/* decl_list ::= decl decl_list
             |  decl */
std::vector<std::unique_ptr<DeclASTnode>> ParseDeclList() {
  std::vector<TOKEN_TYPE> decl_list_first = {INT_TOK, FLOAT_TOK, BOOL_TOK, VOID_TOK};
  std::vector<std::unique_ptr<DeclASTnode>> decl_list;
  if (!TokenContains(decl_list_first, CurTok.type)) {
    PrintParserError("Expected at least one declaration in decl_list.");
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
std::vector<std::unique_ptr<VarDeclASTnode>> ParseLocalDecls() {
  std::vector<std::unique_ptr<VarDeclASTnode>> var_decls;
  std::vector<TOKEN_TYPE> var_decl_first = {INT_TOK, FLOAT_TOK, BOOL_TOK};
  while (TokenContains(var_decl_first, CurTok.type)) {
    auto var_decl = ParseVarDecl();
    var_decls.push_back(std::move(var_decl));
  }
  return std::move(var_decls);
}

std::vector<std::unique_ptr<StmtASTnode>> ParseStmtList(); // forward declaring ParseStmtList since there is a cyclic dependency between ParseBlock and ParseStmtList

// block ::= "{" local_decls stmt_list "}"
std::unique_ptr<BlockASTnode> ParseBlock() {
  // eat '{'
  if (CurTok.type != LBRA) {
    errs() << "Expected block to begin with '{'\n" << "Line # " << lineNo << "\nCur tok: " << CurTok.lexeme; 
    return nullptr;
  }
  getNextToken();
  auto local_decls = ParseLocalDecls();
  auto stmts = ParseStmtList();
  // eat '}'
  if (CurTok.type != RBRA) {
    errs() << "Expected block to end with '}'\n" << "Line # " << lineNo << "\nCur tok: " << CurTok.lexeme; 
    return nullptr;
  }
  getNextToken();
  return std::make_unique<BlockASTnode>(CurTok, std::move(local_decls), std::move(stmts));
}

std::unique_ptr<RValASTnode> ParseRVal(); // forward declaring ParseRVal for ParseExpr

/* expr ::= IDENT "=" expr
        | rval */
std::unique_ptr<ExprASTnode> ParseExpr() {
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
std::unique_ptr<ExprStmtASTnode> ParseExprStmt() {
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
std::unique_ptr<IfStmtASTnode> ParseIfStmt() {
  // eat 'if'
  if (CurTok.type != IF) {
    PrintParserError("Expected if_stmt to begin with 'if'.");
    return nullptr;
  }
  getNextToken();
  // eat '('
  if (CurTok.type != LPAR) {
    PrintParserError("Expected '(' to follow 'if' in if_stmt.");
    return nullptr;
  }
  getNextToken();
  auto condition_expr = ParseExpr();
  // eat ')'
  if (CurTok.type != RPAR) {
    PrintParserError("Expected ')' to follow the if condition expression in if_stmt.");
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

std::unique_ptr<StmtASTnode> ParseStmt(); // forward declaring ParseStmt due to cyclic dependency between ParseWhileStmt and ParseStmt

// while_stmt ::= "while" "(" expr ")" stmt 
std::unique_ptr<WhileStmtASTnode> ParseWhileStmt() {
  // eat 'while'
  if (CurTok.type != WHILE) {
    PrintParserError("Expected while_stmt to begin with 'while'.");
    return nullptr;
  }
  getNextToken();
  // eat '('
  if (CurTok.type != LPAR) {
    PrintParserError("Expected '(' to follow 'while' in while_stmt.");
    return nullptr;
  }
  getNextToken();
  auto condition_expr = ParseExpr();
  // eat ')'
  if (CurTok.type != RPAR) {
    PrintParserError("Expected ')' to follow the while condition expression in while_stmt.");
    return nullptr;
  }
  getNextToken();
  auto body_stmt = ParseStmt();
  return std::make_unique<WhileStmtASTnode>(CurTok, std::move(condition_expr), std::move(body_stmt));
}

// return_stmt ::= "return" expr_stmt
std::unique_ptr<ReturnStmtASTnode> ParseReturnStmt() {
  // eat 'return'
  if (CurTok.type != RETURN) {
    PrintParserError("Expected return_stmt to begin with 'return'.");
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
std::unique_ptr<StmtASTnode> ParseStmt() {
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
  PrintParserError("Expected stmt to be one of an expr_stmt, block, if_stmt, while_stmt or return_stmt, but was none.");
  return nullptr;
}

/* stmt_list ::= stmt stmt_list
             |  epsilon */
std::vector<std::unique_ptr<StmtASTnode>> ParseStmtList() {
  std::vector<std::unique_ptr<StmtASTnode>> stmt_list;
  std::vector<TOKEN_TYPE> stmt_first = {SC, IDENT, MINUS, NOT, LPAR, INT_TOK, FLOAT_TOK, BOOL_TOK, LBRA, IF, WHILE, RETURN};
  while (TokenContains(stmt_first, CurTok.type)) {
    auto stmt = ParseStmt();
    stmt_list.push_back(std::move(stmt));
  }
  return std::move(stmt_list);
}

// extern ::= "extern" type_spec IDENT "(" params ")" ";"
std::unique_ptr<ExternASTnode> ParseExtern() {
  if (CurTok.type != EXTERN) {
    PrintParserError("Expected extern to begin with 'extern'.");
    return nullptr;
  }
  // eat "extern"
  getNextToken();
  // parse type_spec
  auto type_spec = ParseType(true, "type_spec"); // can be void
  // identifier
  if (CurTok.type != IDENT) {
    PrintParserError("Expected IDENT to follow type_spec in extern.");
    return nullptr;
  }
  auto identifier = IdentifierStr;
  // eat identifier
  getNextToken();
  // '('
  if (CurTok.type != LPAR) {
    PrintParserError("Expected '(' to follow IDENT in extern.");
    return nullptr;
  }
  // eat '('
  getNextToken();
  // params
  auto params = ParseParams();
  if (!params) {
    PrintParserError("Expected params to follow '(' in extern.");
    return nullptr;
  }
  // ')'
  if (CurTok.type != RPAR) {
    PrintParserError("Expected ')' to follow params in extern.");
    return nullptr;
  }
  // eat ')'
  getNextToken();
  // ';'
  if (CurTok.type != SC) {
    PrintParserError("Expected ';' to follow ')' in extern.");
    return nullptr;
  }
  // eat ';'
  getNextToken();
  return std::make_unique<ExternASTnode>(std::move(type_spec), identifier, std::move(params));
}

/* extern_list ::= extern extern_list
               |  extern */
std::vector<std::unique_ptr<ExternASTnode>> ParseExternList() {
  std::vector<std::unique_ptr<ExternASTnode>> extern_list;
  auto first_extern = ParseExtern();
  if (!first_extern) {
    PrintParserError("Expected at least one extern in extern_list.");
    return std::vector<std::unique_ptr<ExternASTnode>>();
  }
  extern_list.push_back(std::move(first_extern));
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
std::unique_ptr<ArgListASTnode> ParseArgs() {
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
  return std::make_unique<ArgListASTnode>(std::move(args_expr_list));
}

// element ::= "-" element | "!" element | "(" expr ")" | IDENT | IDENT "(" args ")" | INT_LIT | FLOAT_LIT | BOOL_LIT
std::unique_ptr<ElementASTnode> ParseElement() {
  if (CurTok.type == MINUS || CurTok.type == NOT) {
    // is PrefixOp with unary - or !
    auto op = CurTok;
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
      PrintParserError("Expected ')' to follow the expr inside parenthesis element.");
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
        PrintParserError("Expected ')' after args in a function call.");
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
std::unique_ptr<FactorASTnode> ParseFactor() {
  std::vector<std::unique_ptr<ElementASTnode>> elements;
  std::vector<TOKEN> operators;
  std::vector<TOKEN_TYPE> element_first = {MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT};
  // parse first element
  if (!TokenContains(element_first, CurTok.type)) {
    PrintParserError("Expected factor to begin with at least one element.");
    return nullptr;
  }
  auto first_element = ParseElement();
  elements.push_back(std::move(first_element));
  // parse the rest of the elements separated by operators
  std::vector<TOKEN_TYPE> factor2_first = {ASTERIX, DIV, MOD};
  while (TokenContains(factor2_first, CurTok.type)) {
    auto op = CurTok;
    operators.push_back(op);
    getNextToken();
    auto rhs_element = ParseElement();
    elements.push_back(std::move(rhs_element));
  }
  return std::make_unique<FactorASTnode>(CurTok, std::move(elements), std::move(operators));
}

/* subexpr ::= factor subexpr2
  subexpr2 ::= "+" factor subexpr2 | "-" factor subexpr2 | epsilon */
std::unique_ptr<SubexprASTnode> ParseSubexpr() {
  std::vector<std::unique_ptr<FactorASTnode>> factors;
  std::vector<TOKEN> operators;
  std::vector<TOKEN_TYPE> factor_first = {MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT};
  // parse first element
  if (!TokenContains(factor_first, CurTok.type)) {
    PrintParserError("Expected subexpr to begin with at least one factor.");
    return nullptr;
  }
  auto first_factor = ParseFactor();
  factors.push_back(std::move(first_factor));
  // parse the rest of the factors separated by operators
  std::vector<TOKEN_TYPE> subexpr2_first = {PLUS, MINUS};
  while (TokenContains(subexpr2_first, CurTok.type)) {
    auto op = CurTok;
    operators.push_back(op);
    getNextToken();
    auto rhs_factor = ParseFactor();
    factors.push_back(std::move(rhs_factor));
  }
  return std::make_unique<SubexprASTnode>(CurTok, std::move(factors), std::move(operators));
}

/* rel ::= subexpr rel2
  rel2 ::= "<=" subexpr rel2 | "<" subexpr rel2 | ">=" subexpr rel2 | ">" subexpr rel2 | epsilon */
std::unique_ptr<RelASTnode> ParseRel() {
  std::vector<std::unique_ptr<SubexprASTnode>> subexprs;
  std::vector<TOKEN> operators;
  std::vector<TOKEN_TYPE> subexpr_first = {MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT};
  // parse first element
  if (!TokenContains(subexpr_first, CurTok.type)) {
    PrintParserError("Expected rel to begin with at least one subexpr.");
    return nullptr;
  }
  auto first_subexpr = ParseSubexpr();
  subexprs.push_back(std::move(first_subexpr));
  // parse the rest of the subexprs separated by operators
  std::vector<TOKEN_TYPE> rel2_first = {GT, GE, LT, LE};
  while (TokenContains(rel2_first, CurTok.type)) {
    auto op = CurTok;
    operators.push_back(op);
    getNextToken();
    auto rhs_subexpr = ParseSubexpr();
    subexprs.push_back(std::move(rhs_subexpr));
  }
  return std::make_unique<RelASTnode>(CurTok, std::move(subexprs), std::move(operators));
}

/* equiv ::= rel equiv2
  equiv2 ::= "==" rel equiv2 | "!=" rel equiv2 | epsilon */
std::unique_ptr<EquivASTnode> ParseEquiv() {
  std::vector<std::unique_ptr<RelASTnode>> rels;
  std::vector<TOKEN> operators;
  std::vector<TOKEN_TYPE> rel_first = {MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT};
  // parse first element
  if (!TokenContains(rel_first, CurTok.type)) {
    PrintParserError("Expected equiv to begin with at least one rel.");
    return nullptr;
  }
  auto first_rel = ParseRel();
  rels.push_back(std::move(first_rel));
  // parse the rest of the rels separated by operators
  std::vector<TOKEN_TYPE> equiv2_first = {EQ, NE};
  while (TokenContains(equiv2_first, CurTok.type)) {
    auto op = CurTok;
    operators.push_back(op);
    getNextToken();
    auto rhs_rel = ParseRel();
    rels.push_back(std::move(rhs_rel));
  }
  return std::make_unique<EquivASTnode>(CurTok, std::move(rels), std::move(operators));
}

/* term ::= equiv term2
  term2 ::= "&&" equiv term2 | epsilon */
std::unique_ptr<TermASTnode> ParseTerm() {
  std::vector<std::unique_ptr<EquivASTnode>> equivs;
  std::vector<TOKEN_TYPE> equiv_first = {MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT};
  // parse first element
  if (!TokenContains(equiv_first, CurTok.type)) {
    PrintParserError("Expected term to begin with at least one equiv.");
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
std::unique_ptr<RValASTnode> ParseRVal() {
  std::vector<std::unique_ptr<TermASTnode>> terms;
  std::vector<TOKEN_TYPE> term_first = {MINUS, NOT, LPAR, IDENT, INT_LIT, FLOAT_LIT, BOOL_LIT};
  // parse first element
  if (!TokenContains(term_first, CurTok.type)) {
    PrintParserError("Expected rval to begin with at least one term.");
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
std::unique_ptr<ProgramASTnode> ParseProgram() {
  std::vector<TOKEN_TYPE> decl_list_first = {INT_TOK, FLOAT_TOK, BOOL_TOK, VOID_TOK};
  std::vector<std::unique_ptr<ExternASTnode>> extern_list = CurTok.type == EXTERN ? ParseExternList() : std::vector<std::unique_ptr<ExternASTnode>>();
  if (TokenContains(decl_list_first, CurTok.type)) {
    auto decl_list = ParseDeclList();
    return std::make_unique<ProgramASTnode>(CurTok, std::move(extern_list), std::move(decl_list));
  }
  else {
    PrintParserError("Expected at least one declaration in program.");
  }
  return nullptr;
}

std::unique_ptr<ProgramASTnode> ast;

// program ::= extern_list decl_list | decl_list
static void parser() {
  ast = ParseProgram();
  std::cout << ast->to_string()->ToString(2,2);
}

//===----------------------------------------------------------------------===//
// AST Printer
//===----------------------------------------------------------------------===//

inline llvm::raw_ostream &operator<<(llvm::raw_ostream &os,
                                     const ASTnode &ast) {
  os << ast.to_string()->ToString(2,2);
  // os << "use above when doing";
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

  if (!ast->codegen()) {
    return 1;
  }

  //********************* Start printing final IR **************************
  // Print out all of the generated code into a file called output.ll
  auto Filename = "output.ll";
  std::error_code EC;
  raw_fd_ostream dest(Filename, EC, sys::fs::F_None);

  if (EC) {
    errs() << "Could not open file: " << EC.message();
    return 1;
  }
  TheModule->print(errs(), nullptr); // print IR to terminal
  TheModule->print(dest, nullptr);
  //********************* End printing final IR ****************************

  fclose(pFile); // close the file that contains the code that was parsed
  return 0;
}
