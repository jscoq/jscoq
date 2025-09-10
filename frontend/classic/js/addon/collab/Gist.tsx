import React from "react";
import ReactDOM from "react-dom/client";

import GistComponent from "./GistComponent";
import "./gist.css";

export class Gist {
  editor: any;
  filename: string;

  withCoqManager(coq: any) {
    this.editor = coq.editor.snippets[0]; // ***TODO
    return this;
  }

  static attach(coq: any, gistID: string) {
    const collab = new Gist().withCoqManager(coq);
    collab.init(gistID);
    return collab;
  }

  init(gistID: string) {
    const rootElement = document.getElementById("gist-root");
    const root = ReactDOM.createRoot(rootElement);
    root.render(
      <React.StrictMode>
        <GistComponent gist={this} startGistID={gistID}/>
      </React.StrictMode>
    );
  }

  setFile(filename: string, content: string) {
    this.filename = filename;
    this.editor.load(content, this.filename);
  }

  getContent() {
    return this.editor.editor.getValue();
  }

  getFilename() {
    return this.filename;
  }
}
