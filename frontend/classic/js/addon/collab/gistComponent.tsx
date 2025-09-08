import { Octokit } from "@octokit/core";
import { useEffect, useState } from "react";

interface Gist {
  setFile(filename: string, content: string): void;
  getContent(): string;
  getFilename(): string;
}

/**
 * documentation :
 * https://docs.github.com/en/rest/gists/gists?apiVersion=2022-11-28
 */

const octokitRead = new Octokit({ auth: "" });

type File = {
  idx: number;
  filename: string;
  content: string;
};

const defaultFile: File = { idx: 0, filename: "filename1", content: "" };

type FileProps = {
  file: File;
};

function File({ file }: FileProps) {
  return (
    <>
      <div className="file">
        <h3 className="filename">
          {file.idx + 1}: {file.filename}
        </h3>
        <pre className="file-content">{file.content}</pre>
      </div>
    </>
  );
}

type FilesProps = {
  files: File[];
};

function Files({ files }: FilesProps) {
  let all_file = files.map((f) => {
    return <File key={f.idx} file={f} />;
  });
  return (
    <>
      <div className="file-container">{all_file}</div>
    </>
  );
}

type NotifProps = {
  notif: string;
  setNotif: any;
};

function Notif({ notif, setNotif }: NotifProps) {
  return (
    <div id="notif" hidden={notif === ""}>
      <button id="close-notif" onClick={() => setNotif("")}>
        &times;
      </button>
      &nbsp;{notif}
    </div>
  );
}

function makeErrorMessage(err: any) {
  let status = err.status;
  let message: string;
  if (err.response && err.response.data) {
    message = err.response.data.message;
  } else {
    message = "";
  }
  return "Error " + status + " " + message;
}

type InputProps = {
  id: string;
  value: string;
  onChange: any;
  label?: string;
  placeholder?: string;
  type?: string;
};

function Input({ id, value, onChange, label, placeholder, type }: InputProps) {
  let labelElem = label && <label htmlFor={id}>{label}</label>;
  return (
    <div>
      {label && labelElem}
      <input
        id={id}
        value={value}
        onChange={onChange}
        placeholder={placeholder ?? ""}
        type={type ?? "text"}
      />
    </div>
  );
}

type SaveButtonProps = {
  gist: Gist;
  text: string;
  octokit: Octokit;
  requestRoute: string;
  requestOptions: any;
  onFulfilled: any;
  onRejected: any;
};

function SaveButton({
  gist,
  text,
  octokit,
  requestRoute,
  requestOptions,
  onFulfilled,
  onRejected,
}: SaveButtonProps) {
  return (
    <button
      onClick={() =>
        octokit
          .request(requestRoute, {
            ...requestOptions,
            files: { [gist.getFilename()]: { content: gist.getContent() } },
          })
          .then(onFulfilled)
          .catch(onRejected)
      }
    >
      {text}
    </button>
  );
}

function buttonsElem(
  gist: Gist,
  gistID: string,
  setGistID: any,
  showAll: boolean,
  setShowAll: any,
  octokit: Octokit,
  setNotif: any,
  files: File[],
  setFiles: any
) {
  let showButton = (
    <button onClick={() => setShowAll(!showAll)}>
      {showAll ? "Hide all files" : "Show all files"}
    </button>
  );

  let linkButton = (
    <a href={"https://gist.github.com/" + gistID} target="_blank">
      <button>Go to Gist</button>
    </a>
  );

  let createButton = (
    <SaveButton
      gist={gist}
      text={"Create"}
      octokit={octokit}
      requestRoute={"POST /gists"}
      requestOptions={{
        headers: { "X-GitHub-Api-Version": "2022-11-28" },
      }}
      onFulfilled={(result: any) => {
        setNotif("Created");
        setGistID(result.data.id);
        /* @ts-ignore */
        const url = new URL(location);
        url.searchParams.set("gist", gistID);
        history.pushState({}, "", url);
      }}
      onRejected={(err: any) => {
        console.log(err);
        setNotif(makeErrorMessage(err));
      }}
    />
  );

  let updateButton = (
    <SaveButton
      gist={gist}
      text={"Update"}
      octokit={octokit}
      requestRoute={"PATCH /gists/" + gistID}
      requestOptions={{
        gist_id: gistID,
        headers: { "X-GitHub-Api-Version": "2022-11-28" },
      }}
      onFulfilled={() => {
        setNotif("Updated");
        setFiles(files.map((f, i) => {
          if (i === 0)
            return {...f, content: gist.getContent()};
          return f;
        }))
      }}
      onRejected={(err: any) => {
        console.log(err);
        setNotif(makeErrorMessage(err));
      }}
    />
  );

  return (
    <div>
      {showButton}
      {linkButton}
      {createButton}
      {updateButton}
    </div>
  );
}

type AppProps = {
  gist: Gist;
  startGistID?: string;
};

export default function GistComponent({gist, startGistID}: AppProps) {
  const [token, setToken]: [string, any] = useState(
    ""
  );
  const octokitWrite = new Octokit({ auth: token });
  const [showAll, setShowAll]: [boolean, any] = useState(false);
  const [gistID, setGistID]: [string, any] = useState(startGistID ?? "");
  const [files, setFiles]: [File[], any] = useState([defaultFile]);
  const [notif, setNotif]: [string, any] = useState("");

  useEffect(() => {
    if (gistID === "") {
      setFiles([defaultFile]);
      if (gist)
        gist.setFile(defaultFile.filename, defaultFile.content);
    } else {
      octokitRead
        .request("GET /gists/" + gistID, {
          gist_id: gistID,
          headers: { "X-GitHub-Api-Version": "2022-11-28" },
        })
        .then((result) => {
          let rawFiles = result.data.files;
          setFiles(
            Object.keys(rawFiles).map((f, i) => {
              return { idx: i, filename: f, content: rawFiles[f].content };
            })
          );
          if (Object.keys(rawFiles).length >= 1) {
            let fn = Object.keys(rawFiles)[0];
            gist.setFile(fn, rawFiles[fn].content);
          }
          /* @ts-ignore */
          const url = new URL(location);
          url.searchParams.set("gist", gistID);
          history.pushState({}, "", url);
        })
        .catch((err) => {
          console.log(err);
          setNotif(makeErrorMessage(err));
          setFiles([]);
          gist.setFile(defaultFile.filename, "");
        });
    }
  }, [gistID]);

  let allButtons = buttonsElem(
    gist,
    gistID,
    setGistID,
    showAll,
    setShowAll,
    octokitWrite,
    setNotif,
    files,
    setFiles
  );

  let allFiles = <Files files={files} />;

  return (
    <div className="App">
      <Notif notif={notif} setNotif={setNotif} />
      <div className="input-container">
        <Input
          id={"input-id"}
          value={gistID}
          onChange={(e: any) => setGistID(e.target.value.trim())}
          label={"Gist ID:"}
          placeholder={"gist id"}
        />
        <Input
          id={"input-token"}
          value={token}
          onChange={(e: any) => setToken(e.target.value.trim())}
          label={"Gist Token:"}
          placeholder={"gist write token"}
          type={"password"}
        />
      </div>
      {allButtons}
      {showAll && allFiles}
    </div>
  );
}
