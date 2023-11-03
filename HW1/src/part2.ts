import * as R from "ramda";


const stringToArray = R.split("");

export const countLetters = (s: string) => 
R.countBy(R.toLower)(stringToArray(s).filter(letter=>"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".includes(letter)));


const pop = (s: string[], leftpar: string, rightpar: string): string[] =>
    R.isEmpty(s) ? [rightpar] :
    R.head(s) === leftpar ? R.tail(s) : R.prepend(rightpar, s);

const isPairedReducer = (s: string[], letter: string): string[] =>
    letter === "{" || letter === "[" || letter === "(" ? R.prepend(letter, s) :
    letter === "}" ? pop(s, "{", letter) :
    letter === "]" ? pop(s, "[", letter) :
    letter === ")" ? pop(s, "(", letter) :
    s;

export const isPaired: (s: string) => boolean = R.pipe(
    stringToArray,
    R.reduce(isPairedReducer, []),
    R.isEmpty
);

export interface WordTree {
    root: string;
    children: WordTree[];
}

export const treeToSentence = (tree: WordTree): string =>
    (tree.children.length === 0) ? tree.root : R.slice(0, mapper(tree).length, mapper(tree))


const mapper = (tree: WordTree): string => 
    R.replace(/,/g, " ", (tree.root + " " + R.map(treeToSentence, tree.children)))
