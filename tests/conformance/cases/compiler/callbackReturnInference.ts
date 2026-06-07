// @target: es2022

declare function useCallback<T>(callback: () => T): T;
declare function configure<T>(options: { create: () => T }): T;

const callbackValue = useCallback(() => 1);
const objectCallbackValue = configure({ create: () => ({ value: 1 }) });