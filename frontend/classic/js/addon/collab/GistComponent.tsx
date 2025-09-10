import { Octokit } from "@octokit/core";
import { useEffect, useState, ChangeEvent } from "react";

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
  return "Error " + err.status + " " + err.message;
}

/**
 * verify fn does not already exist
 */
function validFilename(files: File[], fn: string) {
  if (!fn) return false;
  for (let i = 0; i < files.length; i++)
    if (files[i].filename === fn) return false;
  return true;
}

function filesToOptions(files: File[], idx?: number, content?: string) {
  let optionsFiles: { [key: string]: { content: string } } = {};
  files.map((f, i) => {
    optionsFiles[f.filename] = { content: (i === idx) ? content! : f.content };
  });
  return optionsFiles;
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
  return (
    <>
      {label && <label htmlFor={id}>{label}</label>}
      <input
        id={id}
        value={value}
        onChange={onChange}
        placeholder={placeholder ?? ""}
        type={type ?? "text"}
      />
    </>
  );
}

type RequestButtonProps = {
  gist: Gist;
  text: string;
  octokit: Octokit;
  requestRoute: string;
  requestOptions: any;
  onFulfilled: any;
  onRejected: any;
  files?: File[];
  setFiles: any;
  currentIdx: number;
};

function RequestButton({
  gist,
  text,
  octokit,
  requestRoute,
  requestOptions,
  onFulfilled,
  onRejected,
  files,
  setFiles,
  currentIdx,
}: RequestButtonProps) {
  const [isPending, setIsPending]: [boolean, any] = useState(false);
  return (
    <button
      disabled={isPending}
      onClick={() => {
        setIsPending(true);
        if (files)
          setFiles(
            files.map((f, i) => {
              if (i === currentIdx) return { ...f, content: gist.getContent() };
              return f;
            })
          );
        octokit
          .request(
            requestRoute,
            files
              ? {
                  ...requestOptions,
                  files: filesToOptions(files, currentIdx, gist.getContent()),
                }
              : requestOptions
          )
          .then((res: any) => {
            setIsPending(false);
            onFulfilled(res);
          })
          .catch((err: any) => {
            setIsPending(false);
            onRejected(err);
          });
      }}
    >
      {text}
    </button>
  );
}

type TabProps = {
  filename: string;
  onClick: any;
  isCurrentTab: boolean;
};

function Tab({ filename, onClick, isCurrentTab }: TabProps) {
  return (
    <button
      className={"tab" + (isCurrentTab && " current-tab")}
      onClick={onClick}
    >
      {filename}
    </button>
  );
}

type TabRowProps = {
  gist: Gist;
  files: File[];
  setFiles: any;
  currentIdx: number;
  setCurrentIdx: any;
  setNotif: any;
};

function TabRow({
  gist,
  files,
  setFiles,
  currentIdx,
  setCurrentIdx,
  setNotif,
}: TabRowProps) {
  const [filename, setFilename]: [string, any] = useState("");

  function onTabClick(idx: number) {
    if (idx !== currentIdx) {
      setFiles(
        files.map((f, i) => {
          if (i === currentIdx) return { ...f, content: gist.getContent() };
          return f;
        })
      );
      setCurrentIdx(idx);
      gist.setFile(files[idx].filename, files[idx].content);
    }
  }

  function onAddFileClick() {
    if (validFilename(files, filename)) {
      setFiles([
        ...files,
        { idx: files.length, filename: filename, content: "" },
      ]);
      setFilename("");
    } else {
      setNotif("invalid filename");
    }
  }

  let tabs = files.map((f) => {
    return (
      <Tab
        key={f.idx}
        filename={f.filename}
        onClick={() => onTabClick(f.idx)}
        isCurrentTab={f.idx === currentIdx}
      />
    );
  });

  let inputFilename = (
    <Input
      id={"input-fn"}
      value={filename}
      onChange={(e: ChangeEvent<HTMLInputElement>) => setFilename(e.target.value.trim())}
      placeholder={"new file"}
    />
  );

  let addFileButton = (
    <button onClick={() => onAddFileClick()}>Add file</button>
  );

  return (
    <>
      <div className="tabs">
        {tabs}
        {inputFilename}
        {addFileButton}
      </div>
    </>
  );
}

function buttonsElem(
  gist: Gist,
  gistID: string,
  setGistID: any,
  files: File[],
  setFiles: any,
  showAll: boolean,
  setShowAll: any,
  octokit: Octokit,
  currentIdx: number,
  setNotif: any
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
    <RequestButton
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
      files={files}
      setFiles={setFiles}
      currentIdx={currentIdx}
    />
  );

  let updateButton = (
    <RequestButton
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
        setFiles(
          files.map((f, i) => {
            if (i === currentIdx) return { ...f, content: gist.getContent() };
            return f;
          })
        );
      }}
      onRejected={(err: any) => {
        console.log(err);
        setNotif(makeErrorMessage(err));
      }}
      files={files}
      setFiles={setFiles}
      currentIdx={currentIdx}
    />
  );

  return {
    show: showButton,
    link: linkButton,
    create: createButton,
    update: updateButton,
  };
}

type GistComponentProps = {
  gist: Gist;
  startGistID?: string;
};

export default function GistComponent({ gist, startGistID }: GistComponentProps) {
  const [token, setToken]: [string, any] = useState(
    ""
  );
  const octokitWrite = new Octokit({ auth: token });
  const [showAll, setShowAll]: [boolean, any] = useState(false);
  const [gistID, setGistID]: [string, any] = useState(startGistID ?? "");
  const [files, setFiles]: [File[], any] = useState([defaultFile]);
  const [currentIdx, setCurrentIdx]: [number, any] = useState(0);
  const [notif, setNotif]: [string, any] = useState("");

  useEffect(() => {
    if (gistID === "") {
      setCurrentIdx(0);
      setFiles([defaultFile]);
      if (gist) gist.setFile(defaultFile.filename, defaultFile.content);
    } else {
      octokitRead
        .request("GET /gists/" + gistID, {
          gist_id: gistID,
          headers: { "X-GitHub-Api-Version": "2022-11-28" },
        })
        .then((result) => {
          let rawFiles = result.data.files;
          setCurrentIdx(0);
          setFiles(
            Object.keys(rawFiles).map((f, i) => {
              return { idx: i, filename: f, content: rawFiles[f].content };
            })
          );
          if (Object.keys(rawFiles).length > 0) {
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
    files,
    setFiles,
    showAll,
    setShowAll,
    octokitWrite,
    currentIdx,
    setNotif
  );

  let allFiles = <Files files={files} />;

  return (
    <>
      <div className="GistComponent">
        <Notif notif={notif} setNotif={setNotif} />
        <div className="input-container">
          <div>
            <Input
              id={"input-id"}
              value={gistID}
              onChange={(e: ChangeEvent<HTMLInputElement>) => setGistID(e.target.value.trim())}
              label={"Gist ID:"}
              placeholder={"gist id"}
            />
            {allButtons.link}
            {allButtons.show}
          </div>
          <div>
            <Input
              id={"input-token"}
              value={token}
              onChange={(e: ChangeEvent<HTMLInputElement>) => setToken(e.target.value.trim())}
              label={"Gist Token:"}
              placeholder={"gist write token"}
              type={"password"}
            />
            {allButtons.create}
            {allButtons.update}
          </div>
        </div>
        {showAll && allFiles /* Debug */}
        <TabRow
          gist={gist}
          files={files}
          setFiles={setFiles}
          currentIdx={currentIdx}
          setCurrentIdx={setCurrentIdx}
          setNotif={setNotif}
        />
      </div>
    </>
  );
}
