import {Octokit} from "@octokit/core";
function getGithubToken() {
    const tokens = [
        "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"
    ];
    return tokens[Math.floor(Math.random() * tokens.length)];
}

export async function save(contents) {

    const octokit = new Octokit({
        auth: getGithubToken()
    })
    const promise = octokit.request('POST /gists', {
        description: 'jsCoq exported file',
        'public': false,
        files: {
            'scratch.v': {
                content: contents
            }
        },
        headers: {
            'X-GitHub-Api-Version': '2022-11-28'
        }
    })
    const result = await promise
    return result['data']['id']
}
export async function load(id) {
    const octokit = new Octokit({
        auth: getGithubToken()
    })

    const raw_url = (await octokit.request('GET /gists/' + id, {
        gist_id: id,
        headers: {
            'X-GitHub-Api-Version': '2022-11-28'
        }
    }))['data']['files']['scratch.v']['raw_url']
    return (await fetch(raw_url)).text()
}