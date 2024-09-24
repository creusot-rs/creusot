import { workspace, ExtensionContext, Range, Uri, window } from "vscode";
import * as vscode from "vscode";
import * as os from "os";

import {
    DocumentUri,
    LanguageClient,
    LanguageClientOptions,
    NotificationType,
    RequestType,
    ServerOptions,
    Executable,
} from "vscode-languageclient/node";
import { access, existsSync } from "fs";
import { runInContext } from "vm";

const server : Executable = {
    command: "/home/sam/rust/cide/_build/default/server/bin/main.exe",
}

const languages = [
    { scheme: "file", language: "rust" },
    { scheme: "file", language: "coma" },
    { scheme: "file", language: "why3session" },
];

function startServer() : LanguageClient {
    const outputChannel = vscode.window.createOutputChannel("Creusot IDE");
    const traceOutputChannel = vscode.window.createOutputChannel("Creusot IDE Trace");
    const clientOptions : LanguageClientOptions = {
        outputChannel,
        traceOutputChannel,
        documentSelector: languages,
        synchronize: {},
    };
    const client = new LanguageClient("creusot-ide", "Creusot IDE", server, clientOptions);
    client.start();
    return client;
}

type RawPosition = {line: number, character: number}
type RawRange = {start: RawPosition, end: RawPosition}
type RawLocation = {uri: string, range: RawRange}

const mkPosition = (raw : RawPosition) => new vscode.Position(raw.line, raw.character)
const mkRange = (raw : RawRange) => new vscode.Range(mkPosition(raw.start), mkPosition(raw.end))
const mkLocation = (raw : RawLocation) => new vscode.Location(Uri.parse(raw.uri), mkRange(raw.range))

export function activate(context: ExtensionContext) {
    const client = startServer();
    const disposable = vscode.commands.registerCommand("creusot.openFile", async (file) => {
        const uri = Uri.file(file);
        const document = await workspace.openTextDocument(uri);
        await window.showTextDocument(document);
    })
    context.subscriptions.push(disposable);
    const peekLocationsDisposable = vscode.commands.registerCommand("creusot.peekLocations", async (rawUri, rawPosition, rawLocations : Array<RawLocation>) => {
        const uri = Uri.parse(rawUri)
        const position = mkPosition(rawPosition)
        const locations = rawLocations.map(mkLocation)
        await vscode.commands.executeCommand("editor.action.peekLocations", uri, position, locations, "peek")
    })
    context.subscriptions.push(peekLocationsDisposable);
}
