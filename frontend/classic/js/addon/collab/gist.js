import {Octokit} from "@octokit/core";
function getGithubToken() {
    const tokens = [
        atob("Z2l0aHViX3BhdF8xMUJBRzIzTkkwOERoSmQ1Ym9Za3Q5X09Gb293ajR4b0huZ1dQMzNuczRIbUNBZ0V2eTJVNTR4MWU3QkNNWE5nbG5IN1JaSjNFQmhLbEtaU3pm")
    ];
    return tokens[Math.floor(Math.random() * tokens.length)];
}

export class Gist {
    withCoqManager(coq) {
        this.editor = coq.provider.snippets[0];
        return this;
    }
    async save() {
        const octokit = new Octokit({
            auth: getGithubToken()
        });
        const promise = octokit.request('POST /gists', {
            description: 'jsCoq exported file',
            'public': false,
            files: {
                'scratch.v': {
                    content: this.editor.editor.getValue()
                }
            },
            headers: {
                'X-GitHub-Api-Version': '2022-11-28'
            }
        });
        const result = await promise;
        return result.data.id;
    }
    async load(key) {
        const octokit = new Octokit({
            auth: getGithubToken()
        });

        const raw_url = (await octokit.request('GET /gists/' + key, {
            gist_id: key,
            headers: {
                'X-GitHub-Api-Version': '2022-11-28'
            }
        })).data.files['scratch.v'].raw_url;
        const text = (await fetch(raw_url)).text();
        this.editor.load(text, 'from gist');
        return text;
    }

    static async attach(coq, key) {
        const collab = new Gist().withCoqManager(coq);
        if (key) await collab.load(key);
        return collab;
    }
}
