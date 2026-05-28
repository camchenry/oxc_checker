export declare const dataTagSymbol: unique symbol;
export type dataTagSymbol = typeof dataTagSymbol;
export declare const dataTagErrorSymbol: unique symbol;
export type dataTagErrorSymbol = typeof dataTagErrorSymbol;
export declare const unsetMarker: unique symbol;
export type UnsetMarker = typeof unsetMarker;
export type AnyDataTag = {
	[dataTagSymbol]: any;
	[dataTagErrorSymbol]: any;
};
