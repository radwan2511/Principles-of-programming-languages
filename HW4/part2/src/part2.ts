import { getConstantValue, isParenthesizedExpression } from "typescript";

export const MISSING_KEY = '___MISSING_KEY___'
export const MISSING_TABLE_SERVICE = '___MISSING_TABLE_SERVICE___'

//export type Table<T> = Readonly<Record<string, Readonly<T>>>

export type Table<T> = Record<string, T>


export type TableService<T> = {
    get(key: string): Promise<T>;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
}


// Q 2.1 (a)
export function makeTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>): TableService<T> {
    // optional initialization code

    const table : Record<string, Readonly<T>> = {
    };

    return {
        get(key: string): Promise<T> {
            return new Promise<T>((resolve, reject) => { 
                sync().then( table => {
                
                const v = table[key]
                typeof v !== 'undefined' ? resolve(v) : reject(MISSING_KEY)
              })
            })
        },
        set(key: string, val: T): Promise<void> {
            return new Promise<void>((resolve) => {
                sync().then( table => {
                    table[key] = val
                    sync(table)
                    resolve()
                })
            })
        },
        delete(key: string): Promise<void> {
            return new Promise<void>((resolve, reject) => {
                sync().then( table => {
                delete table[key] ? resolve() : reject(MISSING_KEY)
                sync(table)
                })
            })
        }
    }
}

// Q 2.1 (b)
export function getAll<T>(store: TableService<T>, keys: string[]): Promise<T[]> {
    const promises = keys.map(key => store.get(key))
    return Promise.all(promises)
}


// Q 2.2
export type Reference = { table: string, key: string }

export type TableServiceTable = Table<TableService<object>>

export function isReference<T>(obj: T | Reference): obj is Reference {
    return typeof obj === 'object' && 'table' in obj
}

export async function constructObjectFromTables(tables: TableServiceTable, ref: Reference) {
    async function deref(ref: Reference) {
        //return Promise.reject('not implemented')
        if(!(ref.table in tables)){
            return Promise.reject(MISSING_TABLE_SERVICE)
        }
        let obj:any = await tables[ref.table].get(ref.key)
        for (let [key,val] of Object.entries( obj)) {
            if(isReference(val)){
                obj[key]= await deref(val)
            }
        }
        return Promise.resolve(obj)  
    }

    return deref(ref)
}

// Q 2.3

export function lazyProduct<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    return function* () {
        for (const v of g1()) {
            for (const s of g2()) {
                yield [v,s]
            }
        }
    }
}

export function lazyZip<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    return function* () {
        const list1 = [...g1()]
        const list2 = [...g2()]
        for(let i =0 ; i < list1.length; i++){
        yield [list1[i], list2[i]]
        }
        
    }
}

// Q 2.4
export type ReactiveTableService<T> = {
    get(key: string): T;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
    subscribe(observer: (table: Table<T>) => void): void
}

export async function makeReactiveTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>, optimistic: boolean): Promise<ReactiveTableService<T>> {
    // optional initialization code

    let _table: Table<T> = await sync()


    let observers:any = []
    const handleMutation = async (newTable: Table<T>) => {
        if(optimistic){
            for (let obs of observers) {
                obs(newTable)
            }
            await sync (newTable).then((goodtable)=> _table =goodtable).catch(()=>{ 
              for (let obs of observers) {
                  obs(_table)
              }
                return Promise.reject("__EXPECTED_FAILURE__")} )

        }
        else{
            await sync(newTable)
            for (let obs of observers) {
              obs(newTable)     
          }
          _table= newTable
          return Promise.resolve()

        }



    }
    return {
        get(key: string): T {
            if (key in _table) {
                return _table[key]
            } else {
                throw MISSING_KEY
            }
        },
        set(key: string, val: T): Promise<void> {
            const unfrozenTable = JSON.parse(JSON.stringify(_table));
            unfrozenTable[key]=val
            return handleMutation(unfrozenTable)
        },
        delete(key: string): Promise<void> {
            const unfrozenTable = JSON.parse(JSON.stringify(_table));
            delete unfrozenTable[key]
            return handleMutation(unfrozenTable)
        },

        subscribe(observer: (table: Table<T>) => void): void {
            observers.push(observer)
        }
    }
}