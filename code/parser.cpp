/// ASTnode - Base class for all AST nodes.
class ASTnode {
public:
    virtual ~ASTnode() {}
    virtual Value *codegen() = 0;
    virtual std::string to_string() const {}
};
/// IntASTnode - Class for integer literals like 1, 2, 10,
class IntASTnode : public ASTnode {
    int Val; TOKEN Tok;
    public: IntASTnode(TOKEN tok, int val) :Tok(tok), Val(val) { }
};  