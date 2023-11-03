// L5-typecheck
// ========================================================
import { equals, filter, flatten, includes, map, intersection, zipWith, reduce, T, forEach } from 'ramda';
import { isAppExp, isBoolExp, isDefineExp, isIfExp, isLetrecExp, isLetExp, isNumExp,
         isPrimOp, isProcExp, isProgram, isStrExp, isVarRef, unparse, parseL51,
         AppExp, BoolExp, DefineExp, Exp, IfExp, LetrecExp, LetExp, NumExp, SetExp, LitExp,
         Parsed, PrimOp, ProcExp, Program, StrExp, isSetExp, isLitExp, 
         isDefineTypeExp, isTypeCaseExp, DefineTypeExp, TypeCaseExp, CaseExp, makeNumExp, makeDefineTypeExp, makeDottedPair, makeCaseExp, VarDecl } from "./L5-ast";
import { applyTEnv, makeEmptyTEnv, makeExtendTEnv, TEnv } from "./TEnv";
import { isProcTExp, makeBoolTExp, makeNumTExp, makeProcTExp, makeStrTExp, makeVoidTExp,
         parseTE, unparseTExp, Record,
         BoolTExp, NumTExp, StrTExp, TExp, VoidTExp, UserDefinedTExp, isUserDefinedTExp, UDTExp, 
         isNumTExp, isBoolTExp, isStrTExp, isVoidTExp,
         isRecord, ProcTExp, makeUserDefinedNameTExp, Field, makeAnyTExp, isAnyTExp, isUserDefinedNameTExp, makeUserDefinedTExp, isTVar, eqTVar, isConcreteUserDefinedTypeName, parseUserDefinedType } from "./TExp";
import { isEmpty, allT, first, rest, cons } from '../shared/list';
import { Result, makeFailure, bind, makeOk, zipWithResult, mapv, mapResult, isFailure, either, safe2, isOk } from '../shared/result';
import { isNumber, isString } from '../shared/type-predicates';
import { isEmptySExp, isSymbolSExp, makeCompoundSExp, makeSymbolSExp } from './L5-value';
import { isCompoundSexp } from '../shared/parser';
import { timingSafeEqual } from 'crypto';
import { makeExtEnv } from './L5-env';

// L51
export const getTypeDefinitions = (p: Program): UserDefinedTExp[] => {
    const iter = (head: Exp, tail: Exp[]): UserDefinedTExp[] =>
        isEmpty(tail) && isDefineTypeExp(head) ? [head.udType] :
        isEmpty(tail) ? [] :
        isDefineTypeExp(head) ? cons(head.udType, iter(first(tail), rest(tail))) :
        iter(first(tail), rest(tail));
    return isEmpty(p.exps) ? [] :
        iter(first(p.exps), rest(p.exps));
}

// L51
export const getDefinitions = (p: Program): DefineExp[] => {
    const iter = (head: Exp, tail: Exp[]): DefineExp[] =>
        isEmpty(tail) && isDefineExp(head) ? [head] :
        isEmpty(tail) ? [] :
        isDefineExp(head) ? cons(head, iter(first(tail), rest(tail))) :
        iter(first(tail), rest(tail));
    return isEmpty(p.exps) ? [] :
        iter(first(p.exps), rest(p.exps));
}

// L51
export const getRecords = (p: Program): Record[] =>
    flatten(map((ud: UserDefinedTExp) => ud.records, getTypeDefinitions(p)));

// L51
export const getItemByName = <T extends {typeName: string}>(typeName: string, items: T[]): Result<T> =>
    isEmpty(items) ? makeFailure(`${typeName} not found`) :
    first(items).typeName === typeName ? makeOk(first(items)) :
    getItemByName(typeName, rest(items));

// L51
export const getUserDefinedTypeByName = (typeName: string, p: Program): Result<UserDefinedTExp> =>
    getItemByName(typeName, getTypeDefinitions(p));

// L51
export const getRecordByName = (typeName: string, p: Program): Result<Record> =>
    getItemByName(typeName, getRecords(p));

// L51
// Given the name of record, return the list of UD Types that contain this record as a case.
export const getRecordParents = (typeName: string, p: Program): UserDefinedTExp[] =>
    filter((ud: UserDefinedTExp): boolean => map((rec: Record) => rec.typeName, ud.records).includes(typeName),
        getTypeDefinitions(p));


// L51
// Given a user defined type name, return the Record or UD Type which it names.
// (Note: TS fails to type check either in this case)
export const getTypeByName = (typeName: string, p: Program): Result<UDTExp> => {
    const ud = getUserDefinedTypeByName(typeName, p);
    if (isFailure(ud)) {
        return getRecordByName(typeName, p);
    } else {
        return ud;
    }
}

// TODO L51
// Is te1 a subtype of te2?
const isSubType = (te1: TExp, te2: TExp, p: Program): boolean => {
    if(te1 === te2)
    {
        return true;
    }

    if(isUserDefinedNameTExp(te1) && isUserDefinedNameTExp(te2)){
        // let type1 = getTypeByName(te1.typeName,p);
        // let type2 = getTypeByName(te2.typeName,p);

        // let definedType1 = getUserDefinedTypeByName(te1.typeName,p);
        // let definedType2 = getUserDefinedTypeByName(te2.typeName,p);

        // let rec1 = getRecordByName(te1.typeName,p);
        // let rec2 = getRecordByName(te2.typeName,p);
        
        let type1p = getRecordParents(te1.typeName,p);
        let type2p = getRecordParents(te2.typeName,p);
        
        if(type1p.length > 0){
            for (let parent of type1p) {
                if (parent.typeName == te2.typeName) {
                    true;
                }
            }
        }
    }

    if(isUserDefinedNameTExp(te1), isNumTExp(te2)){
        return true;
    }

    if(isUserDefinedNameTExp(te1), isAnyTExp(te2)){
        return true;
    }

    if(isNumTExp(te1), isAnyTExp(te2)){
        return true;
    }
    
    return false;
}
    //false;


// TODO L51: Change this definition to account for user defined types
// Purpose: Check that the computed type te1 can be accepted as an instance of te2
// test that te1 is either the same as te2 or more specific
// Deal with case of user defined type names 
// Exp is only passed for documentation purposes.
// p is passed to provide the context of all user defined types
export const checkEqualType = (te1: TExp, te2: TExp, exp: Exp, p: Program): Result<TExp> => {
    if (equals(te1, te2))
    {
        return makeOk(te2);
    }
    if(isUserDefinedNameTExp(te1) && isUserDefinedNameTExp(te2)){
        // let type1 = getTypeByName(te1.typeName,p);
        // let type2 = getTypeByName(te2.typeName,p);

        // let definedType1 = getUserDefinedTypeByName(te1.typeName,p);
        // let definedType2 = getUserDefinedTypeByName(te2.typeName,p);

        // let rec1 = getRecordByName(te1.typeName,p);
        // let rec2 = getRecordByName(te2.typeName,p);
        
        let type1p = getRecordParents(te1.typeName,p);
        let type2p = getRecordParents(te2.typeName,p);
        
        if(type1p.length > 0){
            for (let parent of type1p) {
                if (parent.typeName == te2.typeName) {
                    return makeOk(te2);
                }
            }
        }

        // if(type2p.length > 0){
        //     for (let parent of type2p) {
        //         if (parent.typeName == te1.typeName) {
        //             return makeOk(te1);
        //         }
        //     }
        // }


    }

    if(isAnyTExp(te2) && isUserDefinedNameTExp(te1))
    {
        return makeOk(te2);
    }
    // if(isAnyTExp(te1) && isUserDefinedNameTExp(te2))
    // {
    //     return makeOk(te1);
    // }

    if(isAnyTExp(te2) && isNumTExp(te1))
    {
        return makeOk(te2);
    }
    // if(isAnyTExp(te1) && isNumExp(te2))
    // {
    //     return makeOk(te1);
    // }

    return makeFailure(`Incompatible types: ${te1} and ${te2} in ${exp}`);
};
    // equals(te1, te2) ? makeOk(te2) :
    //te1 === undefined ? bind(unparseTExp(te2), (texp: string) => makeFailure(`Incompatible types: undefined - ${texp}`)):
    // (isUserDefinedNameTExp(te1) && isUserDefinedNameTExp(te2) ) ? isRecord() ?
    //  ? makeOk(te2):
    // && checkUserDefinedTypes(p)
    //isTVar(te1) && isTVar(te2) ? ((eqTVar(te1, te2) ? makeOk(true) : checkTVarEqualTypes(te1, te2, exp))) :
    // isTVar(te1) ? checkTVarEqualTypes(te1, te2, exp) :
    // isTVar(te2) ? checkTVarEqualTypes(te2, te1, exp) :
    // isAtomicTExp(te1) && T.isAtomicTExp(te2) ?
    //     eqAtomicTExp(te1, te2) ? makeOk(true) : safe2((te1: string, te2: string) => makeFailure<true>(`Incompatible atomic types ${te1} - ${te2}`))
    //                                                 (T.unparseTExp(te1), T.unparseTExp(te2)) :
    // isProcTExp(te1) && T.isProcTExp(te2) ? checkProcEqualTypes(te1, te2, exp) :
    
    // // L51
    // isClassTExp(te1) && T.isClassTExp(te2) ? checkClassEqualTypes(te1, te2, exp) :
    // // A class can match a proc (symbol -> T) if the symbol is bound and is in the interface of the class
    // isClassTExp(te1) && T.isProcTExp(te2) ? checkClassProcEqualTypes(te1, te2, exp) :
    // isClassTExp(te2) && T.isProcTExp(te1) ? checkClassProcEqualTypes(te2, te1, exp) :
    //safe2((te1: string, te2: string) => makeFailure<true>(`Incompatible types structure: ${te1} - ${te2}`))
    //    (T.unparseTExp(te1), T.unparseTExp(te2));
    
    //makeFailure(`Incompatible types: ${te1} and ${te2} in ${exp}`);


// L51
// Return te and its parents in type hierarchy to compute type cover
// Return type names (not their definition)
export const getParentsType = (te: TExp, p: Program): TExp[] =>
    (isNumTExp(te) || isBoolTExp(te) || isStrTExp(te) || isVoidTExp(te) || isAnyTExp(te)) ? [te] :
    isProcTExp(te) ? [te] :
    isUserDefinedTExp(te) ? [te] :
    isRecord(te) ? getParentsType(makeUserDefinedNameTExp(te.typeName), p) :
    isUserDefinedNameTExp(te) ?
        either(getUserDefinedTypeByName(te.typeName, p),
                (ud: UserDefinedTExp) => [makeUserDefinedNameTExp(ud.typeName)],
                (_) => either(getRecordByName(te.typeName, p),
                            (rec: Record) => cons(makeUserDefinedNameTExp(rec.typeName), 
                                                  map((ud) => makeUserDefinedNameTExp(ud.typeName), 
                                                      getRecordParents(rec.typeName, p))),
                            (_) => [])) : 
    [];

// L51
// Get the list of types that cover all ts in types.
export const coverTypes = (types: TExp[], p: Program): TExp[] => 
    // [[p11, p12], [p21], [p31, p32]] --> types in intersection of all lists
    ((parentsList: TExp[][]): TExp[] => reduce<TExp[],TExp[]>(intersection, first(parentsList), rest(parentsList)))
     (map((t) => getParentsType(t,p), types));

// Return the most specific in a list of TExps
// For example given UD(R1, R2):
// - mostSpecificType([R1, R2, UD]) = R1 (choses first out of record level)
// - mostSpecificType([R1, number]) = number  
export const mostSpecificType = (types: TExp[], p: Program): TExp =>
    reduce((min: TExp, element: TExp) => isSubType(element, min, p) ? element : min, 
            makeAnyTExp(),
            types);

// L51
// Check that all t in types can be covered by a single parent type (not by 'any')
// Return most specific parent
export const checkCoverType = (types: TExp[], p: Program): Result<TExp> => {
    const cover = coverTypes(types, p);
    return isEmpty(cover) ? makeFailure(`No type found to cover ${map((t) => JSON.stringify(unparseTExp(t), null, 2), types).join(" ")}`) :
    makeOk(mostSpecificType(cover, p));
}


// Compute the initial TEnv given user defined types
// =================================================
// TODO L51
// Construct type environment for the user-defined type induced functions
// Type constructor for all records
// Type predicate for all records
// Type predicate for all user-defined-types
// All globally defined variables (with define)

// TODO: Define here auxiliary functions for TEnv computation

// TOODO L51
// Initialize TEnv with:
// * Type of global variables (define expressions at top level of p)
// * Type of implicitly defined procedures for user defined types (define-type expressions in p)
export const initTEnv = (p: Program): TEnv => {
    
    const typePredGen = (): ProcTExp => makeProcTExp( [makeAnyTExp()]  , makeBoolTExp());
    const recordsConstructorGen = (rec: Record , p:Program): ProcTExp =>{
        const type:Result<UDTExp>  = getTypeByName(rec.typeName ,p);
        const fieldsType:TExp[] = map((field:Field) => field.te , rec.fields);
        if (isOk(type))
           return makeProcTExp( fieldsType  , makeUserDefinedNameTExp(type.value.typeName) )    // return makeProcTExp( fieldsType  , type.value)
        else
            return makeProcTExp( fieldsType , makeAnyTExp() );
    } 


    const typeDef: UserDefinedTExp[] = getTypeDefinitions(p)
    const records: Record[] = getRecords(p)
    const initialEnv:TEnv = makeEmptyTEnv();
    const  definitions: DefineExp[] = getDefinitions(p);

    const definitionsNames:string[] = map( (def:DefineExp) => def.var.var , definitions);
    const definitionsType: TExp[] = map((def:DefineExp) => def.var.texp , definitions);

    const UDPredicatesNames:string[] = map((UD: UserDefinedTExp) => `${UD.typeName}?` , typeDef);
    const UDPredicates:ProcTExp[] = map(  (UD: UserDefinedTExp) => typePredGen() , typeDef);

    const recordsPredicatesNames:string[] = map(  (rec: Record) => `${rec.typeName}?` , records);
    const recordsPredicates:ProcTExp[] = map(  (rec: Record) => typePredGen() , records);

    const recordsConstructorsNames:string[] = map(  (rec: Record) => `make-${rec.typeName}` , records);
    const recordsConstructors:ProcTExp[] = map(  (rec: Record) => recordsConstructorGen(rec , p) , records);
    

    const functionsNames:string[] = [...UDPredicatesNames , ...recordsPredicatesNames , ...recordsConstructorsNames , ...definitionsNames];
    const functions:TExp[] = [...UDPredicates , ...recordsPredicates , ...recordsConstructors , ...definitionsType];

    return makeExtendTEnv(functionsNames , functions , initialEnv);



    


}
    //makeEmptyTEnv();


// Verify that user defined types and type-case expressions are semantically correct
// =================================================================================
// TODO L51
const checkUserDefinedTypes = (p: Program): Result<true> =>
    // If the same type name is defined twice with different definitions
    // If a recursive type has no base case
    {
        const getAllRecordsByName: ((rec:Record , records:Record[])=> Record[]) = (rec:Record, records:Record[]) => filter ((currRec:Record) => currRec.typeName ===  rec.typeName  , records);
        const hasSameFields: ((records:Record[], first:Record) => boolean) = (records:Record[] , first:Record) => reduce((acc , curr)=> (acc && equals(curr.fields ,first.fields)),true,records);
        const isRecursive: (UDtype:UserDefinedTExp) => boolean = (UDtype:UserDefinedTExp) => UDtype.records.some((rec:Record) => rec.fields.some((field:Field) => equals(field.te , makeUserDefinedNameTExp(UDtype.typeName)) ))   
        const hasBaseCase: (UDtype:UserDefinedTExp) => boolean = (UDtype:UserDefinedTExp) => UDtype.records.some((rec:Record) => rec.fields.every((field:Field) => !equals(field.te , makeUserDefinedNameTExp(UDtype.typeName)) ))   
        const isGoodUDType: (UDtype:UserDefinedTExp) => boolean = (UDtype:UserDefinedTExp) => !isRecursive(UDtype) || (isRecursive(UDtype) && hasBaseCase(UDtype));
        const UDtypes:UserDefinedTExp[] = getTypeDefinitions(p);
        const records:Record[] = getRecords(p);
            //condition 1
        const constraint1: boolean = reduce (  (acc:boolean ,curr:Record) => curr && hasSameFields( getAllRecordsByName(curr , records) , curr)  , true , records)
    
            //condition 2
        const constraint2: boolean = reduce ( (acc: boolean, curr: UserDefinedTExp) =>  acc && isGoodUDType(curr) , true ,UDtypes);
        
        return (constraint1 && constraint2) ?makeOk(true) : makeFailure("one of the constraints is false");




    }
    

// TODO L51
const checkTypeCase = (tc: TypeCaseExp, p: Program): Result<true> => 
    // Check that all type case expressions have exactly one clause for each constituent subtype 
    // (in any order)
    {
        //makeOk(true);
    let cases = tc.cases

    for(let c of cases){
        if(c.typeName == tc.typeName)
        {
            return makeOk(true);
        }
    }

    let a = getUserDefinedTypeByName(tc.typeName,p)
    let records
    if (isFailure(a))
        return a
    else
        records = a.value.records
    
    for (let i = 0; i < cases.length; i++) {
        let b = records.filter((x)=>x.typeName == cases[i].typeName)
        if (b.length != 1){
            return makeFailure("fail")
        }
        else if(b[0].fields.length != cases[i].varDecls.length){
            return makeFailure("fail")
        }  
    }
    return makeOk(true);
    }
    


// Compute the type of L5 AST exps to TE
// ===============================================
// Compute a Typed-L5 AST exp to a Texp on the basis
// of its structure and the annotations it contains.

// Purpose: Compute the type of a concrete fully-typed expression
export const L51typeofProgram = (concreteExp: string): Result<string> =>
    bind(parseL51(concreteExp), (p: Program) =>
        bind(typeofExp(p, initTEnv(p), p), unparseTExp));

// For tests on a single expression - wrap the expression in a program
export const L51typeof = (concreteExp: string): Result<string> =>
    L51typeofProgram(`(L51 ${concreteExp})`);

// Purpose: Compute the type of an expression
// Traverse the AST and check the type according to the exp type.
// We assume that all variables and procedures have been explicitly typed in the program.
export const typeofExp = (exp: Parsed, tenv: TEnv, p: Program): Result<TExp> =>
    isNumExp(exp) ? makeOk(typeofNum(exp)) :
    isBoolExp(exp) ? makeOk(typeofBool(exp)) :
    isStrExp(exp) ? makeOk(typeofStr(exp)) :
    isPrimOp(exp) ? typeofPrim(exp) :
    isVarRef(exp) ? applyTEnv(tenv, exp.var) :
    isIfExp(exp) ? typeofIf(exp, tenv, p) :
    isProcExp(exp) ? typeofProc(exp, tenv, p) :
    isAppExp(exp) ? typeofApp(exp, tenv, p) :
    isLetExp(exp) ? typeofLet(exp, tenv, p) :
    isLetrecExp(exp) ? typeofLetrec(exp, tenv, p) :
    isDefineExp(exp) ? typeofDefine(exp, tenv, p) :
    isProgram(exp) ? typeofProgram(exp, tenv, p) :
    isSetExp(exp) ? typeofSet(exp, tenv, p) :
    isLitExp(exp) ? typeofLit(exp, tenv, p) :
    isDefineTypeExp(exp) ? typeofDefineType(exp, tenv, p) :
    isTypeCaseExp(exp) ? typeofTypeCase(exp, tenv, p) :
    makeFailure(`Unknown type: ${JSON.stringify(exp, null, 2)}`);

// Purpose: Compute the type of a sequence of expressions
// Check all the exps in a sequence - return type of last.
// Pre-conditions: exps is not empty.
export const typeofExps = (exps: Exp[], tenv: TEnv, p: Program): Result<TExp> =>
    isEmpty(rest(exps)) ? typeofExp(first(exps), tenv, p) :
    bind(typeofExp(first(exps), tenv, p), _ => typeofExps(rest(exps), tenv, p));

// a number literal has type num-te
export const typeofNum = (n: NumExp): NumTExp => makeNumTExp();

// a boolean literal has type bool-te
export const typeofBool = (b: BoolExp): BoolTExp => makeBoolTExp();

// a string literal has type str-te
const typeofStr = (s: StrExp): StrTExp => makeStrTExp();

// primitive ops have known proc-te types
const numOpTExp = parseTE('(number * number -> number)');
const numCompTExp = parseTE('(number * number -> boolean)');
const boolOpTExp = parseTE('(boolean * boolean -> boolean)');

// L51 Todo: cons, car, cdr, list 
export const typeofPrim = (p: PrimOp): Result<TExp> =>
    (p.op === '+') ? numOpTExp :
    (p.op === '-') ? numOpTExp :
    (p.op === '*') ? numOpTExp :
    (p.op === '/') ? numOpTExp :
    (p.op === 'and') ? boolOpTExp :
    (p.op === 'or') ? boolOpTExp :
    (p.op === '>') ? numCompTExp :
    (p.op === '<') ? numCompTExp :
    (p.op === '=') ? numCompTExp :
    // Important to use a different signature for each op with a TVar to avoid capture
    (p.op === 'number?') ? parseTE('(T -> boolean)') :
    (p.op === 'boolean?') ? parseTE('(T -> boolean)') :
    (p.op === 'string?') ? parseTE('(T -> boolean)') :
    (p.op === 'list?') ? parseTE('(T -> boolean)') :
    (p.op === 'pair?') ? parseTE('(T -> boolean)') :
    (p.op === 'symbol?') ? parseTE('(T -> boolean)') :
    (p.op === 'not') ? parseTE('(boolean -> boolean)') :
    (p.op === 'eq?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'string=?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'display') ? parseTE('(T -> void)') :
    (p.op === 'newline') ? parseTE('(Empty -> void)') :
    (p.op === 'car') ? parseTE('(cons -> T)') :
    (p.op === 'cdr') ? parseTE('(cons -> T)') :
    (p.op === 'cons') ? parseTE('(T1 * T2 -> cons)') :
    makeFailure(`Primitive not yet implemented: ${p.op}`);

// TODO L51
// Change this definition to account for possibility of subtype expressions between thenTE and altTE
// 
// Purpose: compute the type of an if-exp
// Typing rule:
//   if type<test>(tenv) = boolean
//      type<then>(tenv) = t1
//      type<else>(tenv) = t1
// then type<(if test then else)>(tenv) = t1
export const typeofIf = (ifExp: IfExp, tenv: TEnv, p: Program): Result<TExp> => {
    const testTE = typeofExp(ifExp.test, tenv, p);
    const thenTE = typeofExp(ifExp.then, tenv, p);
    const altTE = typeofExp(ifExp.alt, tenv, p);
    const constraint1 = bind(testTE, testTE => checkEqualType(testTE, makeBoolTExp(), ifExp, p));
    const constraint2 = bind(thenTE, (thenTE: TExp) =>
                            bind(altTE, (altTE: TExp) =>
                                checkEqualType(thenTE, altTE, ifExp, p)));
    return bind(constraint1, (_c1) => constraint2);
};

// Purpose: compute the type of a proc-exp
// Typing rule:
// If   type<body>(extend-tenv(x1=t1,...,xn=tn; tenv)) = t
// then type<lambda (x1:t1,...,xn:tn) : t exp)>(tenv) = (t1 * ... * tn -> t)
export const typeofProc = (proc: ProcExp, tenv: TEnv, p: Program): Result<TExp> => {
    const argsTEs = map((vd) => vd.texp, proc.args);
    const extTEnv = makeExtendTEnv(map((vd) => vd.var, proc.args), argsTEs, tenv);
    const constraint1 = bind(typeofExps(proc.body, extTEnv, p), (body: TExp) => 
                            checkEqualType(body, proc.returnTE, proc, p));
    return bind(constraint1, (returnTE: TExp) => makeOk(makeProcTExp(argsTEs, returnTE)));
};

// Purpose: compute the type of an app-exp
// Typing rule:
// If   type<rator>(tenv) = (t1*..*tn -> t)
//      type<rand1>(tenv) = t1
//      ...
//      type<randn>(tenv) = tn
// then type<(rator rand1...randn)>(tenv) = t
// We also check the correct number of arguments is passed.
export const typeofApp = (app: AppExp, tenv: TEnv, p: Program): Result<TExp> =>
    bind(typeofExp(app.rator, tenv, p), (ratorTE: TExp) => {
        if (! isProcTExp(ratorTE)) {
            return bind(unparseTExp(ratorTE), (rator: string) =>
                        bind(unparse(app), (exp: string) =>
                            makeFailure<TExp>(`Application of non-procedure: ${rator} in ${exp}`)));
        }
        if (app.rands.length !== ratorTE.paramTEs.length) {
            return bind(unparse(app), (exp: string) => makeFailure<TExp>(`Wrong parameter numbers passed to proc: ${exp}`));
        }
        const constraints = zipWithResult((rand, trand) => bind(typeofExp(rand, tenv, p), (typeOfRand: TExp) => 
                                                                checkEqualType(typeOfRand, trand, app, p)),
                                          app.rands, ratorTE.paramTEs);
        return mapv(constraints, _ => ratorTE.returnTE);
    });

// Purpose: compute the type of a let-exp
// Typing rule:
// If   type<val1>(tenv) = t1
//      ...
//      type<valn>(tenv) = tn
//      type<body>(extend-tenv(var1=t1,..,varn=tn; tenv)) = t
// then type<let ((var1 val1) .. (varn valn)) body>(tenv) = t
export const typeofLet = (exp: LetExp, tenv: TEnv, p: Program): Result<TExp> => {
    const vars = map((b) => b.var.var, exp.bindings);
    const vals = map((b) => b.val, exp.bindings);
    const varTEs = map((b) => b.var.texp, exp.bindings);
    const constraints = zipWithResult((varTE, val) => bind(typeofExp(val, tenv, p), (typeOfVal: TExp) => 
                                                            checkEqualType(varTE, typeOfVal, exp, p)),
                                      varTEs, vals);
    return bind(constraints, _ => typeofExps(exp.body, makeExtendTEnv(vars, varTEs, tenv), p));
};

// Purpose: compute the type of a letrec-exp
// We make the same assumption as in L4 that letrec only binds proc values.
// Typing rule:
//   (letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)
//   tenv-body = extend-tenv(p1=(t11*..*t1n1->t1)....; tenv)
//   tenvi = extend-tenv(xi1=ti1,..,xini=tini; tenv-body)
// If   type<body1>(tenv1) = t1
//      ...
//      type<bodyn>(tenvn) = tn
//      type<body>(tenv-body) = t
// then type<(letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)>(tenv-body) = t
export const typeofLetrec = (exp: LetrecExp, tenv: TEnv, p: Program): Result<TExp> => {
    const ps = map((b) => b.var.var, exp.bindings);
    const procs = map((b) => b.val, exp.bindings);
    if (! allT(isProcExp, procs))
        return makeFailure(`letrec - only support binding of procedures - ${JSON.stringify(exp, null, 2)}`);
    const paramss = map((p) => p.args, procs);
    const bodies = map((p) => p.body, procs);
    const tijs = map((params) => map((p) => p.texp, params), paramss);
    const tis = map((proc) => proc.returnTE, procs);
    const tenvBody = makeExtendTEnv(ps, zipWith((tij, ti) => makeProcTExp(tij, ti), tijs, tis), tenv);
    const tenvIs = zipWith((params, tij) => makeExtendTEnv(map((p) => p.var, params), tij, tenvBody),
                           paramss, tijs);
    const types = zipWithResult((bodyI, tenvI) => typeofExps(bodyI, tenvI, p), bodies, tenvIs)
    const constraints = bind(types, (types: TExp[]) => 
                            zipWithResult((typeI, ti) => checkEqualType(typeI, ti, exp, p), types, tis));
    return bind(constraints, _ => typeofExps(exp.body, tenvBody, p));
};

// TODO - write the true definition
// Purpose: compute the type of a define
// Typing rule:
//   (define (var : texp) val)
//   tenv-val = extend-tenv(var:texp; tenv)
// If   type<val>(tenv-val) = texp
// then type<(define (var : texp) val)>(tenv) = void
export const typeofDefine = (exp: DefineExp, tenv: TEnv, p: Program): Result<VoidTExp> => {
    const v = exp.var.var;
    const texp = exp.var.texp;
    const val = exp.val;
    const tenvVal = makeExtendTEnv([v], [texp], tenv);
    const constraint = typeofExp(val, tenvVal, p);    
    return mapv(constraint, (_) => makeVoidTExp());
};

// Purpose: compute the type of a program
// Typing rule:
export const typeofProgram = (exp: Program, tenv: TEnv, p: Program): Result<TExp> =>
    typeofExps(exp.exps, tenv, p);

// TODO L51
// Write the typing rule for DefineType expressions
export const typeofDefineType = (exp: DefineTypeExp, _tenv: TEnv, _p: Program): Result<TExp> => {
    // for(let e of _p.exps){
    //     if(e.tag == exp.tag && e.typeName == exp.typeName)
    //     {
    //         return makeOk(makeVoidTExp());
    //     }
    // }
    
    const constraint = checkUserDefinedTypes(_p)


    return bind(constraint,()=> makeOk(exp.udType))
    //return makeFailure(`Todo ${JSON.stringify(exp, null, 2)}`);
}
        
//makeFailure(`Todo ${JSON.stringify(exp, null, 2)}`);

// TODO L51
export const typeofSet = (exp: SetExp, _tenv: TEnv, _p: Program): Result<TExp> =>{
    const constraint = bind(typeofExp(exp.val, _tenv, _p), 
                            (valTE: TExp) => bind(applyTEnv(_tenv, exp.var.var),(varTE: TExp) => checkEqualType(varTE, valTE, exp, _p)));
    return bind(constraint, _ => makeOk(makeVoidTExp()));
};
    //makeFailure(`Todo ${JSON.stringify(exp, null, 2)}`);

// TODO L51
export const typeofLit = (exp: LitExp, _tenv: TEnv, _p: Program): Result<TExp> => 
    isNumber(exp.val) ?  makeOk(makeNumTExp()) :
    exp.val === true ? makeOk(makeBoolTExp()) :
    exp.val === false ? makeOk(makeBoolTExp()) :
    isString(exp.val) ? makeOk(makeStrTExp()) :
    isEmptySExp(exp.val) ? makeOk(makeVoidTExp()) :
    isUserDefinedNameTExp(exp.val) ? makeOk(makeUserDefinedNameTExp(exp.val.typeName)):


    makeFailure(`Unknown literal type ${exp}`);

// TODO: L51
// Purpose: compute the type of a type-case
// Typing rule:
// For all user-defined-type id
//         with component records record_1 ... record_n
//         with fields (field_ij) (i in [1...n], j in [1..R_i])
//         val CExp
//         body_i for i in [1..n] sequences of CExp
//   ( type-case id val (record_1 (field_11 ... field_1r1) body_1)...  )
//  TODO
export const typeofTypeCase = (exp: TypeCaseExp, tenv: TEnv, p: Program): Result<TExp> => {
    
    const getCaseVarNames:(cas:CaseExp) => string[] = (cas:CaseExp) => map((vd: VarDecl) => vd.var ,  cas.varDecls); 

    const getCaseVarTypes:(cas:CaseExp , p:Program) => TExp[] = (cas:CaseExp ,  p:Program) =>   {
    const rec:Result<Record> = getRecordByName(cas.typeName , p);
    return isOk(rec) ? map ((fi:Field) => fi.te , rec.value.fields) : [];
    }


    const constraint1:Result<true> = checkTypeCase(exp ,p );
    
        const typeOfCorrectTypeCase: (exp: TypeCaseExp) => Result<TExp> = (exp: TypeCaseExp) => {
            const cases:CaseExp[] = exp.cases;
            const newEnv = makeExtendTEnv(getCaseVarNames(cases[0]),getCaseVarTypes(cases[0] , p),tenv)
            const typeOfFirstCase = typeofExps(cases[0].body, newEnv ,p);
            // const constraint2 = cases.every( (cas:CaseExp) => {
            //     const typeCurr = typeofExps(cas.body,makeExtendTEnv(getCaseVarNames(cas),getCaseVarTypes(cas , p),tenv),p)

            //     return equals (typeofExps(cas.body,makeExtendTEnv(getCaseVarNames(cas),getCaseVarTypes(cas , p),tenv),p) , typeOfFirstCase )
            // } )
            
            let constraint2 = false;
            let constraint3 = false;
            //let ret = null;
            for (let cas of cases){
                constraint3 = equals (typeofExps(cas.body,makeExtendTEnv(getCaseVarNames(cas),getCaseVarTypes(cas , p),tenv),p) , typeOfFirstCase )
                if(equals (typeofExps(cas.body,makeExtendTEnv(getCaseVarNames(cas),getCaseVarTypes(cas , p),tenv),p) , typeOfFirstCase ))
                {
                    constraint2 = true;
                    //ret = typeofExps(cas.body, newEnv ,p);
                    //ret = getRecordParents(cas.typeName,p);
                }
            }
            if(constraint3 == false && constraint2 == true){
                let ret : UserDefinedTExp[] = getRecordParents(cases[0].typeName,p);
                for(let r of ret){
                    for(let record of r.records){
                        if(record.typeName == cases[0].typeName)
                        {
                            return makeOk(makeUserDefinedNameTExp(r.typeName));
                        }
                    }
                }
            }

            return constraint2 ? typeOfFirstCase : makeFailure("case types are not equal"); 
        }
    
        return bind (constraint1 , (constraint1Res:boolean) => typeOfCorrectTypeCase(exp))

}
