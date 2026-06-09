function makeActionCreator(type: string) {
    function actionCreator(payload: string) {
        return { type, payload };
    }

    actionCreator.type = type;
    actionCreator.match = (value: unknown): value is { type: string } => typeof value === "object" && value !== null && "type" in value;

    const creatorType = actionCreator.type;
    const matcher = actionCreator.match;
    const result = actionCreator("value");
    return actionCreator;
}

const returnedCreator = makeActionCreator("demo");
const returnedType = returnedCreator.type;
const returnedMatch = returnedCreator.match({ type: "demo" });
const returnedResult = returnedCreator("payload");

const arrowCreator = (payload: number) => ({ payload });
let arrowLabel = "arrow";
arrowCreator.type = arrowLabel;
arrowCreator.match = (value: unknown): value is { payload: number } => true;

const arrowType = arrowCreator.type;
const arrowMatch = arrowCreator.match;
const arrowResult = arrowCreator(1);
